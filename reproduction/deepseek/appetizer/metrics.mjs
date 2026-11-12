// Local accounting only. Never persist headers, request/response bodies or errors
// supplied by a provider: those can contain credentials and source material.
import http from 'node:http';
import { once } from 'node:events';
import {
  appendFileSync, chmodSync, closeSync, existsSync, fsyncSync, mkdirSync,
  openSync, readFileSync, renameSync, writeFileSync,
} from 'node:fs';
import { createHash, randomUUID, timingSafeEqual } from 'node:crypto';
import { join } from 'node:path';

export const SERVICE = 'appetizer-clean-openrouter-meter-v3';
export const PHASES = ['setup', 'formalization'];
export const UPSTREAM = 'https://openrouter.ai/api/v1';
export const MODEL = 'deepseek/deepseek-v4.1-flash-1017';
const number = x => typeof x === 'number' && Number.isFinite(x) && x >= 0 ? x : null;
const tokenCount = x => Number.isSafeInteger(x) && x >= 0 ? x : null;
const identifier = x => typeof x === 'string' && /^[a-zA-Z0-9_.:/ -]{1,160}$/.test(x)
  && !/sk-or-|Bearer/i.test(x) ? x : null;
export const generationId = x => typeof x === 'string' && /^gen-[a-zA-Z0-9-]{1,124}$/.test(x) ? x : null;
const now = () => new Date().toISOString();
const rounded = x => Number(x.toFixed(12));

function statistics(requests, bills, active, end) {
  const total = field => rounded(bills.reduce((s, r) => s + (r[field] ?? 0), 0));
  const missing = field => bills.filter(r => r[field] === undefined).length;
  const lostIntervals = requests.filter(r => !r.ended_at && !active.has(r.request_id));
  const intervals = requests.filter(r => r.ended_at || active.has(r.request_id))
    .map(r => [Date.parse(r.started_at), Date.parse(r.ended_at ?? end)])
    .sort((a, b) => a[0] - b[0]);
  let busy = 0, left = 0, right = 0;
  for (const [a, b] of intervals) {
    if (a > right) { busy += right - left; left = a; right = b; }
    else right = Math.max(right, b);
  }
  busy += right - left;
  const missingCosts = missing('cost_usd');
  const missingInputs = missing('input_tokens'), missingOutputs = missing('output_tokens');
  return {
    api_busy_wall_seconds: lostIntervals.length ? null : busy / 1000,
    known_api_busy_wall_seconds: busy / 1000,
    summed_request_seconds: requests.some(r => r.duration_ms === undefined) ? null
      : rounded(requests.reduce((s, r) => s + r.duration_ms / 1000, 0)),
    missing_request_duration_records: requests.filter(r => r.duration_ms === undefined).length,
    last_api_response_at: requests.map(r => r.ended_at).filter(Boolean).sort().at(-1) ?? null,
    request_count: requests.length, unique_billing_records: bills.length,
    successful_requests: requests.filter(r => r.status === 'completed').length,
    failed_or_interrupted_requests: requests.filter(r => !['completed', 'in_progress'].includes(r.status)).length,
    requests_with_unknown_outcome: lostIntervals.length,
    locally_in_flight: requests.filter(r => active.has(r.request_id)).length,
    input_tokens: missingInputs ? null : total('input_tokens'),
    output_tokens: missingOutputs ? null : total('output_tokens'),
    cost_usd: missingCosts ? null : total('cost_usd'),
    known_input_tokens: total('input_tokens'), known_output_tokens: total('output_tokens'),
    known_cost_usd: total('cost_usd'),
    reported_reasoning_tokens: total('reasoning_tokens'),
    reported_cached_input_tokens: total('cached_input_tokens'),
    missing_input_usage_records: missingInputs, missing_output_usage_records: missingOutputs,
    missing_cost_records: missingCosts,
    accounting_complete: !missingInputs && !missingOutputs && !missingCosts,
  };
}

function writeCsv(file, columns, rows) {
  const csv = [columns.join(','), ...rows.map(r => columns.map(k => {
    const v = r[k] ?? ''; return `"${String(v).replaceAll('"', '""')}"`;
  }).join(','))].join('\n') + '\n';
  mkdirSync(join(file, '..'), { recursive: true, mode: 0o700 });
  writeFileSync(`${file}.tmp`, csv, { mode: 0o600 }); renameSync(`${file}.tmp`, file);
}

export function atomicJson(file, value) {
  mkdirSync(join(file, '..'), { recursive: true, mode: 0o700 });
  const temp = `${file}.${randomUUID()}.tmp`;
  writeFileSync(temp, `${JSON.stringify(value, null, 2)}\n`, { mode: 0o600, flag: 'wx' });
  const fd = openSync(temp, 'r');
  try { fsyncSync(fd); } finally { closeSync(fd); }
  renameSync(temp, file);
  chmodSync(file, 0o600);
}

export function normalizeUsage(usage) {
  if (!usage || typeof usage !== 'object') return {};
  const pairs = {
    input_tokens: tokenCount(usage.prompt_tokens),
    output_tokens: tokenCount(usage.completion_tokens),
    total_tokens: tokenCount(usage.total_tokens),
    reasoning_tokens: tokenCount(usage.completion_tokens_details?.reasoning_tokens),
    cached_input_tokens: tokenCount(usage.prompt_tokens_details?.cached_tokens),
    cache_write_tokens: tokenCount(usage.prompt_tokens_details?.cache_write_tokens),
    cost_usd: number(usage.cost),
  };
  return Object.fromEntries(Object.entries(pairs).filter(([, v]) => v !== null));
}

// Fold SSE cumulatively: each usage block is a snapshot, never an increment.
// StringDecoder in the caller preserves UTF-8 across network chunks.
export class ResponseAccounting {
  constructor(onGeneration = () => {}) {
    this.buffer = ''; this.metadata = {}; this.done = false; this.error = false;
    this.onGeneration = onGeneration;
  }
  accept(value) {
    if (!value || typeof value !== 'object') return;
    const id = generationId(value.id);
    if (id && !this.metadata.generation_id) {
      this.metadata.generation_id = id;
      this.onGeneration(id);
    }
    if (identifier(value.model)) this.metadata.response_model = value.model;
    if (identifier(value.provider)) this.metadata.provider = value.provider;
    Object.assign(this.metadata, normalizeUsage(value.usage));
    for (const choice of value.choices ?? []) {
      if (identifier(choice.finish_reason)) this.metadata.finish_reason = choice.finish_reason;
    }
    if (value.error) this.error = true;
  }
  feed(text, final = false) {
    this.buffer += text;
    // Normalize CRLF even when CR and LF arrive in separate network chunks.
    this.buffer = this.buffer.replace(/\r\n/g, '\n');
    let cut;
    while ((cut = this.buffer.indexOf('\n\n')) >= 0) {
      const event = this.buffer.slice(0, cut);
      this.buffer = this.buffer.slice(cut + 2);
      this.event(event);
    }
    if (final && this.buffer.trim()) { this.event(this.buffer); this.buffer = ''; }
  }
  event(event) {
    const data = event.split('\n').filter(x => x.startsWith('data:'))
      .map(x => x.slice(5).trimStart()).join('\n').trim();
    if (data === '[DONE]') { this.done = true; return; }
    if (!data) return;
    try { this.accept(JSON.parse(data)); } catch { this.error = true; }
  }
}

export class MetricsStore {
  constructor(root, exportRoot, manifest, meterHash) {
    this.root = root; this.exportRoot = exportRoot;
    this.manifest = manifest; this.meterHash = meterHash;
    mkdirSync(join(root, 'runs'), { recursive: true, mode: 0o700 });
    chmodSync(root, 0o700);
    this.active = new Set();
  }
  file(id, name) {
    if (!/^[0-9TZ-]+-[0-9a-f-]{36}$/.test(id)) throw new Error('invalid_run_id');
    return join(this.root, 'runs', id, name);
  }
  readRun(id) { return JSON.parse(readFileSync(this.file(id, 'run.json'), 'utf8')); }
  current() {
    const file = join(this.root, 'current.json');
    return existsSync(file) ? JSON.parse(readFileSync(file, 'utf8')).run_id : null;
  }
  saveRun(run) { atomicJson(this.file(run.run_id, 'run.json'), run); }
  start(label = 'hdp-appetizer-clean', phase = 'formalization') {
    if (!/^[a-zA-Z0-9_-]{1,64}$/.test(label) || /sk-or-|Bearer/i.test(label)) throw new Error('invalid_label');
    if (!PHASES.includes(phase)) throw new Error('invalid_phase');
    const previous = this.current();
    if (previous && this.readRun(previous).state !== 'stopped') throw new Error('run_already_armed_or_running');
    const id = `${now().replace(/[:.]/g, '-')}-${randomUUID()}`;
    const immediate = phase === 'setup', at = now();
    const run = {
      schema_version: 2, run_id: id, label, state: immediate ? 'running' : 'armed', armed_at: at,
      started_at: immediate ? at : null, stopped_at: null, outcome: 'not_recorded',
      start_trigger: immediate ? 'operator_start' : 'first_api_request',
      current_phase: phase,
      phase_intervals: [{ phase_id: randomUUID(), phase, started_at: immediate ? at : null,
        ended_at: null, start_trigger: immediate ? 'operator_start' : 'first_api_request' }],
      manifest: this.manifest, meter_sha256: this.meterHash,
      scope: 'all requests through this dedicated provider, including retries, auxiliary calls and child sessions',
      timing: immediate ? 'wall time starts at the setup start command; includes local installation, tools and idle time'
        : 'wall time starts at the first metered API request; includes local tools and idle time',
    };
    this.saveRun(run);
    atomicJson(join(this.root, 'current.json'), { run_id: id });
    this.export(id);
    return run;
  }
  phase(phase) {
    if (!PHASES.includes(phase)) throw new Error('invalid_phase');
    const id = this.current();
    if (!id) throw new Error('no_experiment');
    const run = this.readRun(id);
    if (run.state === 'stopped') throw new Error('experiment_is_stopped');
    if (this.active.size) throw new Error('requests_in_flight_wait_before_switching_phase');
    if (run.current_phase === phase) return this.export(id); // no timer reset
    const at = now();
    run.phase_intervals ??= [];
    const previous = run.phase_intervals.at(-1);
    if (previous && !previous.ended_at) previous.ended_at = at;
    run.phase_intervals.push({ phase_id: randomUUID(), phase, started_at: at,
      ended_at: null, start_trigger: 'operator_phase_switch' });
    run.current_phase = phase;
    if (!run.started_at) {
      run.started_at = at;
      run.start_trigger = 'operator_phase_switch';
      run.timing = 'wall time starts at the first explicit phase switch; includes local tools and idle time';
    }
    run.state = 'running';
    this.saveRun(run);
    return this.export(id);
  }
  append(id, event) {
    const file = this.file(id, 'events.jsonl');
    const fd = openSync(file, 'a', 0o600);
    try { appendFileSync(fd, `${JSON.stringify({ recorded_at: now(), ...event })}\n`); fsyncSync(fd); }
    finally { closeSync(fd); }
  }
  begin(stream) {
    const id = this.current();
    if (!id) throw new Error('start_experiment_before_sending_prompt');
    const run = this.readRun(id);
    if (run.state === 'stopped') throw new Error('experiment_is_stopped');
    const started = now();
    if (!run.started_at) {
      run.started_at = started; run.state = 'running';
      const interval = run.phase_intervals?.at(-1);
      if (interval && !interval.started_at) interval.started_at = started;
      this.saveRun(run);
    }
    const interval = run.phase_intervals?.at(-1);
    const request = { request_id: randomUUID(), model: MODEL, streamed: stream,
      started_at: started, status: 'in_progress', phase: interval?.phase ?? 'unclassified',
      phase_id: interval?.phase_id ?? null };
    this.append(id, { type: 'request_started', ...request });
    this.active.add(request.request_id);
    return { runId: id, request };
  }
  finish(id, request, result) {
    this.append(id, { type: 'request_finished', request_id: request.request_id, ...result });
    this.active.delete(request.request_id);
    this.export(id);
  }
  requests(id) {
    const file = this.file(id, 'events.jsonl');
    if (!existsSync(file)) return [];
    const rows = new Map();
    for (const line of readFileSync(file, 'utf8').split('\n')) {
      if (!line.trim()) continue;
      let event;
      try { event = JSON.parse(line); } catch { throw new Error('damaged_metrics_ledger'); }
      const { type, recorded_at, ...fields } = event;
      rows.set(event.request_id, { ...rows.get(event.request_id), ...fields });
    }
    return [...rows.values()];
  }
  stop() {
    const id = this.current();
    if (!id) throw new Error('no_experiment');
    if (this.active.size) throw new Error('requests_in_flight_stop_harness_generation_first');
    const run = this.readRun(id);
    if (run.state !== 'stopped') {
      run.state = 'stopped'; run.stopped_at = now(); run.outcome = 'operator_stopped';
      const interval = run.phase_intervals?.at(-1);
      if (interval && !interval.ended_at) interval.ended_at = run.stopped_at;
      this.saveRun(run);
    }
    return this.export(id);
  }
  summary(id) {
    const run = this.readRun(id), requests = this.requests(id);
    // A retried response with the SAME generation id is one bill, not two.
    const charges = new Map();
    for (const r of requests) {
      const key = r.generation_id ?? r.request_id;
      const previous = charges.get(key) ?? {};
      charges.set(key, { ...previous, ...r,
        ...Object.fromEntries(Object.entries(previous).filter(([k]) => r[k] === undefined)),
        billing_phase: previous.billing_phase ?? r.phase ?? 'unclassified' });
    }
    const bills = [...charges.values()];
    const end = run.stopped_at ?? now();
    const names = [...PHASES];
    if (requests.some(r => !r.phase || r.phase === 'unclassified')) names.push('unclassified');
    const phases = Object.fromEntries(names.map(phase => {
      const intervals = (run.phase_intervals ?? []).filter(p => p.phase === phase);
      const rows = requests.filter(r => (r.phase ?? 'unclassified') === phase);
      const phaseBills = bills.filter(b => b.billing_phase === phase);
      return [phase, { phase, currency: 'USD',
        state: phase === 'unclassified' ? 'unclassified' : intervals.some(p => p.started_at && !p.ended_at) ? 'running'
          : intervals.some(p => p.started_at) ? 'stopped' : 'not_started',
        intervals,
        wall_elapsed_seconds: phase === 'unclassified' ? null : rounded(intervals.reduce((sum, p) => sum + (p.started_at
          ? Math.max(0, Date.parse(p.ended_at ?? end) - Date.parse(p.started_at)) / 1000 : 0), 0)),
        ...statistics(rows, phaseBills, this.active, end),
      }];
    }));
    return {
      ...run, generated_at: now(), currency: 'USD',
      wall_elapsed_seconds: run.started_at ? Math.max(0, (Date.parse(end) - Date.parse(run.started_at)) / 1000) : 0,
      ...statistics(requests, bills, this.active, end),
      phases,
      phase_attribution: 'Requests and their whole input/output usage belong to the phase active at dispatch. A repeated generation id is billed once to its first phase. Historical untagged requests remain unclassified.',
      accounting_source: 'OpenRouter response usage; optional generation metadata reconciliation. No list-price estimate.',
      reasoning_note: 'Reasoning and cache counts are reported subsets; never add them to input/output totals.',
      limitations: 'Only this metered endpoint is covered. No claim of mathematical completion. Credit purchase fees and other providers are outside API inference cost.',
    };
  }
  export(id = this.current()) {
    if (!id) return { state: 'not_started', request_count: 0 };
    const summary = this.summary(id), rows = this.requests(id);
    const dir = join(this.exportRoot, id);
    atomicJson(join(dir, 'summary.json'), summary);
    atomicJson(join(dir, 'requests.json'), rows);
    const columns = ['request_id', 'generation_id', 'phase', 'phase_id', 'started_at', 'ended_at', 'model', 'response_model',
      'provider', 'streamed', 'http_status', 'status', 'duration_ms', 'time_to_first_byte_ms',
      'input_tokens', 'output_tokens', 'reasoning_tokens', 'cached_input_tokens', 'cache_write_tokens',
      'cost_usd', 'finish_reason', 'usage_source', 'billing_source'];
    writeCsv(join(dir, 'requests.csv'), columns, rows);
    const phaseRows = Object.values(summary.phases);
    writeCsv(join(dir, 'phases.csv'), ['phase', 'state', 'wall_elapsed_seconds', 'api_busy_wall_seconds',
      'request_count', 'unique_billing_records', 'input_tokens', 'output_tokens', 'cost_usd',
      'known_input_tokens', 'known_output_tokens', 'known_cost_usd', 'missing_cost_records', 'accounting_complete'], phaseRows);
    for (const phase of phaseRows) {
      atomicJson(join(dir, 'phases', phase.phase, 'summary.json'), phase);
      writeCsv(join(dir, 'phases', phase.phase, 'requests.csv'), columns,
        rows.filter(r => (r.phase ?? 'unclassified') === phase.phase));
    }
    atomicJson(join(this.exportRoot, 'latest-summary.json'), summary);
    return summary;
  }
}

function authenticated(actual, expected) {
  if (typeof actual !== 'string') return false;
  const a = Buffer.from(actual), b = Buffer.from(`Bearer ${expected}`);
  return a.length === b.length && timingSafeEqual(a, b);
}
function json(res, code, value) {
  res.writeHead(code, { 'content-type': 'application/json', 'cache-control': 'no-store' });
  res.end(JSON.stringify(value));
}

export async function reconcile(store, id, apiKey, upstream = UPSTREAM) {
  let checked = 0;
  const seen = new Set();
  for (const request of store.requests(id)) {
    if (!request.generation_id || seen.has(request.generation_id)
      || (request.cost_usd !== undefined && request.input_tokens !== undefined && request.output_tokens !== undefined)) continue;
    seen.add(request.generation_id);
    let data;
    for (let attempt = 0; attempt < 3; attempt++) {
      try {
        const response = await fetch(`${upstream}/generation?id=${encodeURIComponent(request.generation_id)}`, {
          headers: { authorization: `Bearer ${await apiKey()}` },
          redirect: 'error', signal: AbortSignal.timeout(15000),
        });
        if (response.ok) { data = (await response.json()).data; break; }
        if (![404, 429, 502, 503].includes(response.status)) break;
      } catch { /* No raw exception may enter logs. Leave missing usage unknown. */ }
      if (attempt < 2) await new Promise(resolve => setTimeout(resolve, (attempt + 1) * 1000));
    }
    if (!data || generationId(data.id) !== request.generation_id) continue;
    const update = { type: 'billing_reconciled', request_id: request.request_id };
    for (const [from, to, convert] of [
      ['native_tokens_prompt', 'input_tokens', tokenCount],
      ['native_tokens_completion', 'output_tokens', tokenCount],
      ['native_tokens_reasoning', 'reasoning_tokens', tokenCount],
      ['native_tokens_cached', 'cached_input_tokens', tokenCount],
      ['total_cost', 'cost_usd', number],
    ]) {
      const v = convert(data[from]);
      if (v !== null && request[to] === undefined) update[to] = v;
    }
    if (update.input_tokens !== undefined || update.output_tokens !== undefined) update.usage_source = 'openrouter_generation_native';
    if (update.cost_usd !== undefined) update.billing_source = 'openrouter_generation_total_cost';
    if (identifier(data.provider_name)) update.provider = data.provider_name;
    store.append(id, update); checked++;
  }
  return { reconciled_records: checked, summary: store.export(id) };
}

export function createMeterServer({ store, apiKey, clientKey = apiKey, controlToken, upstream = UPSTREAM, meterHash }) {
  return http.createServer(async (req, res) => {
    let tracked, started, firstByte, upstreamStatus;
    const abort = new AbortController();
    res.on('close', () => { if (!res.writableEnded) abort.abort(); });
    try {
      // Loopback only, Host checking and no browser Origin. No CORS or cookies.
      if (req.headers.origin || req.headers.host !== `127.0.0.1:${req.socket.localPort}`) {
        return json(res, 403, { error: 'local_meter_access_denied' });
      }
      if (req.method === 'GET' && req.url === '/health') {
        return json(res, 200, { service: SERVICE, meter_sha256: meterHash });
      }
      if (req.url.startsWith('/control/')) {
        if (!authenticated(req.headers.authorization, controlToken)) return json(res, 401, { error: 'unauthorized' });
        if (req.method !== 'POST') return json(res, 405, { error: 'method_not_allowed' });
        if (req.url === '/control/start') {
          return json(res, 200, store.start(req.headers['x-experiment-label'] ?? 'hdp-appetizer-clean',
            req.headers['x-experiment-phase'] ?? 'formalization'));
        }
        if (req.url === '/control/phase') return json(res, 200, store.phase(req.headers['x-experiment-phase']));
        if (req.url === '/control/stop') return json(res, 200, store.stop());
        if (req.url === '/control/status') return json(res, 200, store.export());
        if (req.url === '/control/reconcile') {
          const id = store.current();
          if (!id) return json(res, 409, { error: 'no_experiment' });
          return json(res, 200, await reconcile(store, id, apiKey, upstream));
        }
        return json(res, 404, { error: 'unknown_control' });
      }
      if (req.method !== 'POST' || req.url !== '/api/v1/chat/completions') {
        return json(res, 404, { error: 'unsupported_route' });
      }
      const localKey = await clientKey();
      if (!authenticated(req.headers.authorization, localKey)) return json(res, 401, { error: 'unauthorized' });
      const parts = [];
      for await (const part of req) parts.push(part);
      const bytes = Buffer.concat(parts);
      let body;
      try { body = JSON.parse(bytes.toString('utf8')); }
      catch { return json(res, 400, { error: 'invalid_json' }); }
      if (body.model !== MODEL) return json(res, 400, { error: 'use_the_experiment_model' });
      tracked = store.begin(body.stream === true);
      started = performance.now();
      const accounting = new ResponseAccounting(id => store.append(tracked.runId, {
        type: 'response_metadata', request_id: tracked.request.request_id, generation_id: id,
      }));
      const key = await apiKey();
      const response = await fetch(`${upstream}/chat/completions`, {
        method: 'POST', headers: { authorization: `Bearer ${key}`, 'content-type': 'application/json' },
        body: bytes, redirect: 'error', signal: abort.signal,
      });
      upstreamStatus = response.status;
      const type = response.headers.get('content-type') ?? 'application/json';
      res.writeHead(response.status, { 'content-type': type, 'cache-control': 'no-store' });
      const decoder = new TextDecoder();
      const sse = type.includes('text/event-stream');
      let nonStream = '';
      for await (const chunk of response.body) {
        if (firstByte === undefined) firstByte = performance.now() - started;
        const text = decoder.decode(chunk, { stream: true });
        if (sse) accounting.feed(text); else nonStream += text;
        if (!res.write(chunk)) await once(res, 'drain', { signal: abort.signal });
      }
      const rest = decoder.decode();
      if (sse) accounting.feed(rest, true);
      else {
        try { accounting.accept(JSON.parse(nonStream + rest)); }
        catch { accounting.error = true; }
      }
      const m = accounting.metadata;
      store.finish(tracked.runId, tracked.request, {
        ...m, ended_at: now(), duration_ms: rounded(performance.now() - started),
        time_to_first_byte_ms: firstByte === undefined ? null : rounded(firstByte),
        http_status: response.status,
        status: !response.ok || accounting.error ? 'provider_error' : sse && !accounting.done ? 'interrupted' : 'completed',
        usage_source: 'openrouter_response',
        ...(m.cost_usd !== undefined ? { billing_source: 'openrouter_response_usage_cost' } : {}),
      });
      res.end();
    } catch (error) {
      if (tracked) {
        store.finish(tracked.runId, tracked.request, {
          ended_at: now(), duration_ms: rounded(performance.now() - started),
          time_to_first_byte_ms: firstByte === undefined ? null : rounded(firstByte),
          http_status: upstreamStatus ?? null,
          status: abort.signal.aborted ? 'client_disconnected' : 'transport_error',
        });
      }
      // Only our known machine-readable errors are returned. Never stringify a
      // fetch/credential exception, provider response or incoming header.
      const safe = /^(start_experiment_before_sending_prompt|experiment_is_stopped|run_already_armed_or_running|invalid_label|invalid_phase|no_experiment|requests_in_flight_stop_harness_generation_first|requests_in_flight_wait_before_switching_phase)$/.test(error.message)
        ? error.message : 'meter_operation_failed';
      if (!res.headersSent) json(res, 409, { error: safe }); else res.destroy();
    }
  });
}

export function sourceHash(file) { return createHash('sha256').update(readFileSync(file)).digest('hex'); }
