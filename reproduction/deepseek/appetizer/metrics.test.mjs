import test from 'node:test';
import assert from 'node:assert/strict';
import http from 'node:http';
import { once } from 'node:events';
import { mkdtempSync, readFileSync, readdirSync, rmSync, statSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  MODEL, MetricsStore, ResponseAccounting, createMeterServer, normalizeUsage, reconcile,
} from './metrics.mjs';

const KEY = 'synthetic-test-credential-never-a-real-key';
const CONTROL = 'synthetic-control-token';
const PRIVATE_PROMPT = 'PRIVATE_SOURCE_CONTENT_MUST_NOT_APPEAR_IN_METRICS';
const PRIVATE_OUTPUT = 'PRIVATE_MODEL_OUTPUT_MUST_NOT_APPEAR_IN_METRICS';

function fixture(t) {
  const dir = mkdtempSync(join(tmpdir(), 'appetizer-metrics-test-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return { dir, store: new MetricsStore(join(dir, 'private'), join(dir, 'reports'), { model: MODEL }, 'test-hash') };
}
async function listen(t, server) {
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  t.after(() => { server.closeAllConnections(); server.close(); });
  return `http://127.0.0.1:${server.address().port}`;
}
function files(dir) {
  return readdirSync(dir, { withFileTypes: true }).flatMap(e => e.isDirectory() ? files(join(dir, e.name)) : [join(dir, e.name)]);
}
async function post(base, body) {
  return fetch(`${base}/api/v1/chat/completions`, {
    method: 'POST', headers: { authorization: `Bearer ${KEY}`, 'content-type': 'application/json' },
    body: JSON.stringify({ model: MODEL, messages: [{ role: 'user', content: PRIVATE_PROMPT }], ...body }),
  });
}

test('SSE handles byte boundaries, CRLF, repeated usage snapshots, reasoning and caching without summing twice', () => {
  const ids = [], parser = new ResponseAccounting(id => ids.push(id));
  const usage = { prompt_tokens: 120, completion_tokens: 50, total_tokens: 170, cost: 0.0027,
    prompt_tokens_details: { cached_tokens: 80 }, completion_tokens_details: { reasoning_tokens: 40 } };
  const text = [
    ': keep-alive\r\n\r\n',
    `data: ${JSON.stringify({ id: 'gen-test1', choices: [{ delta: { content: 'λ' } }], usage })}\r\n\r\n`,
    `data: ${JSON.stringify({ id: 'gen-test1', usage, choices: [{ finish_reason: 'stop' }] })}\r\n\r\n`,
    'data: [DONE]\r\n\r\n',
  ].join('');
  const decoder = new TextDecoder();
  for (const byte of Buffer.from(text)) parser.feed(decoder.decode(Uint8Array.of(byte), { stream: true }));
  parser.feed(decoder.decode(), true);
  assert.equal(parser.metadata.input_tokens, 120);
  assert.equal(parser.metadata.output_tokens, 50);
  assert.equal(parser.metadata.reasoning_tokens, 40);
  assert.equal(parser.metadata.cached_input_tokens, 80);
  assert.equal(parser.metadata.cost_usd, 0.0027);
  assert.equal(parser.done, true); assert.equal(parser.error, false);
  assert.deepEqual(ids, ['gen-test1']);
  assert.deepEqual(normalizeUsage({ cost: null, prompt_tokens: null }), {});
});

test('totals deduplicate generations, retain retries, distinguish missing cost from zero, and merge parallel time', t => {
  const { store } = fixture(t), run = store.start();
  const add = (id, gen, start, end, fields) => {
    store.append(run.run_id, { type: 'request_started', request_id: id, generation_id: gen,
      started_at: start, ended_at: end, duration_ms: Date.parse(end) - Date.parse(start), status: 'completed', ...fields });
  };
  add('r1', 'gen-first', '2026-10-31T00:00:00Z', '2026-10-31T00:00:10Z', { input_tokens: 100, output_tokens: 20, cost_usd: 0.01 });
  add('r2', 'gen-first', '2026-10-31T00:00:05Z', '2026-10-31T00:00:15Z', { input_tokens: 100, output_tokens: 20, cost_usd: 0.01 });
  add('r3', 'gen-retry', '2026-10-31T00:00:20Z', '2026-10-31T00:00:25Z', { input_tokens: 110, output_tokens: 25 });
  let s = store.summary(run.run_id);
  assert.equal(s.request_count, 3); assert.equal(s.unique_billing_records, 2);
  assert.equal(s.input_tokens, 210); assert.equal(s.output_tokens, 45);
  assert.equal(s.cost_usd, null); assert.equal(s.known_cost_usd, 0.01); assert.equal(s.missing_cost_records, 1);
  assert.equal(s.api_busy_wall_seconds, 20); assert.equal(s.summed_request_seconds, 25);
  store.append(run.run_id, { type: 'billing_reconciled', request_id: 'r3', cost_usd: 0 });
  s = store.export(run.run_id);
  assert.equal(s.cost_usd, 0.01); assert.equal(s.accounting_complete, true);
});

test('meter transparently forwards streaming and non-streaming requests and writes no secrets or source content', async t => {
  const { dir, store } = fixture(t);
  let upstreamCalls = 0;
  const usage = { prompt_tokens: 91, completion_tokens: 17, cost: 0.00031,
    prompt_tokens_details: { cached_tokens: 20 }, completion_tokens_details: { reasoning_tokens: 12 } };
  const upstream = await listen(t, http.createServer(async (req, res) => {
    assert.equal(req.headers.authorization, `Bearer ${KEY}`);
    let text = ''; for await (const chunk of req) text += chunk;
    const body = JSON.parse(text); assert.equal(body.messages[0].content, PRIVATE_PROMPT);
    upstreamCalls++;
    const obj = { id: `gen-ok${upstreamCalls}`, model: MODEL, usage,
      choices: [{ message: { content: PRIVATE_OUTPUT }, finish_reason: 'stop' }] };
    if (!body.stream) { res.setHeader('content-type', 'application/json'); res.end(JSON.stringify(obj)); }
    else {
      res.setHeader('content-type', 'text/event-stream');
      for (const byte of Buffer.from(`data: ${JSON.stringify(obj)}\r\n\r\ndata: [DONE]\r\n\r\n`)) res.write(Uint8Array.of(byte));
      res.end();
    }
  }));
  const base = await listen(t, createMeterServer({ store, apiKey: async () => KEY, controlToken: CONTROL, upstream, meterHash: 'test-hash' }));
  let response = await post(base, { stream: true });
  assert.equal(response.status, 409); await response.text(); assert.equal(upstreamCalls, 0);
  store.start();
  response = await post(base, { stream: true });
  assert.equal(response.status, 200); assert.match(await response.text(), /PRIVATE_MODEL_OUTPUT/);
  response = await post(base, { stream: false });
  assert.equal((await response.json()).choices[0].message.content, PRIVATE_OUTPUT);
  const summary = store.stop();
  assert.equal(summary.input_tokens, 182); assert.equal(summary.output_tokens, 34);
  assert.equal(summary.cost_usd, 0.00062); assert.equal(summary.successful_requests, 2);
  for (const file of files(dir)) {
    const text = readFileSync(file, 'utf8');
    for (const secret of [KEY, CONTROL, PRIVATE_PROMPT, PRIVATE_OUTPUT]) assert.equal(text.includes(secret), false, file);
    assert.equal(statSync(file).mode & 0o777, 0o600);
  }
  response = await post(base, { stream: false });
  assert.equal(response.status, 409); await response.text(); assert.equal(upstreamCalls, 2);
});

test('HTTP failures, embedded SSE errors and truncated responses remain counted with missing billing unresolved', async t => {
  const { store } = fixture(t); store.start();
  let attempt = 0;
  const upstream = await listen(t, http.createServer((req, res) => {
    req.resume(); attempt++;
    if (attempt === 1) { res.writeHead(429, { 'content-type': 'application/json' }); res.end(JSON.stringify({ error: { message: KEY } })); }
    else {
      res.setHeader('content-type', 'text/event-stream');
      res.end(`data: ${JSON.stringify({ id: `gen-error${attempt}`, ...(attempt === 2 ? { error: { message: PRIVATE_OUTPUT } } : {}) })}\n\n`);
    }
  }));
  const base = await listen(t, createMeterServer({ store, apiKey: async () => KEY, controlToken: CONTROL, upstream, meterHash: 'test-hash' }));
  for (let i = 0; i < 3; i++) { const r = await post(base, { stream: true }); await r.text(); }
  const s = store.stop();
  assert.equal(s.request_count, 3); assert.equal(s.failed_or_interrupted_requests, 3);
  assert.equal(s.cost_usd, null); assert.equal(s.input_tokens, null); assert.equal(s.missing_cost_records, 3);
  const restored = new MetricsStore(store.root, store.exportRoot, {}, 'test-hash');
  assert.equal(restored.summary(s.run_id).missing_cost_records, 3);
});

test('generation reconciliation fills missing native usage and actual cost without duplicating receipts', async t => {
  const { store } = fixture(t); const run = store.start();
  store.append(run.run_id, { type: 'request_started', request_id: 'r1', started_at: new Date().toISOString(),
    generation_id: 'gen-recover', status: 'transport_error' });
  let calls = 0;
  const upstream = await listen(t, http.createServer((req, res) => {
    assert.equal(req.url, '/generation?id=gen-recover'); assert.equal(req.headers.authorization, `Bearer ${KEY}`); calls++;
    res.setHeader('content-type', 'application/json');
    res.end(JSON.stringify({ data: { id: 'gen-recover', native_tokens_prompt: 150, native_tokens_completion: 30,
      native_tokens_reasoning: 20, total_cost: 0.003, provider_name: 'TestProvider', ignored_field: KEY } }));
  }));
  let result = await reconcile(store, run.run_id, async () => KEY, upstream);
  assert.equal(result.summary.input_tokens, 150); assert.equal(result.summary.output_tokens, 30);
  assert.equal(result.summary.cost_usd, 0.003); assert.equal(result.summary.accounting_complete, true);
  result = await reconcile(store, run.run_id, async () => KEY, upstream);
  assert.equal(calls, 1); assert.equal(result.reconciled_records, 0);
});

test('a severed upstream connection preserves its generation id for later billing recovery', async t => {
  const { store } = fixture(t); const run = store.start();
  const upstream = await listen(t, http.createServer((req, res) => {
    req.resume(); res.setHeader('content-type', 'text/event-stream');
    res.write(`data: ${JSON.stringify({ id: 'gen-severed', choices: [{ delta: { content: PRIVATE_OUTPUT } }] })}\n\n`);
    setTimeout(() => res.destroy(), 20);
  }));
  const base = await listen(t, createMeterServer({ store, apiKey: async () => KEY, controlToken: CONTROL, upstream, meterHash: 'test-hash' }));
  const response = await post(base, { stream: true });
  await assert.rejects(response.text());
  const r = store.requests(run.run_id)[0];
  assert.equal(r.generation_id, 'gen-severed'); assert.equal(r.status, 'transport_error');
  assert.equal(store.stop().missing_cost_records, 1);
});

test('crash recovery does not invent an API duration for an unfinished request', t => {
  const { store } = fixture(t); const run = store.start();
  store.begin(true);
  const restored = new MetricsStore(store.root, store.exportRoot, {}, 'test-hash');
  const s = restored.stop();
  assert.equal(s.requests_with_unknown_outcome, 1);
  assert.equal(s.api_busy_wall_seconds, null); assert.equal(s.summed_request_seconds, null);
  assert.equal(s.cost_usd, null); assert.equal(s.accounting_complete, false);
});

test('browser Origins, wrong Host/auth/model and in-flight stop are rejected before forwarding', async t => {
  const { store } = fixture(t); store.start();
  const base = await listen(t, createMeterServer({ store, apiKey: async () => KEY, controlToken: CONTROL,
    upstream: 'http://127.0.0.1:1', meterHash: 'test-hash' }));
  let denied = await fetch(`${base}/health`, { headers: { origin: 'https://evil.test' } });
  assert.equal(denied.status, 403); await denied.text();
  // Node fetch rewrites Host; use the HTTP client to exercise a foreign Host.
  const wrongHostStatus = await new Promise(resolve => {
    http.get(`${base}/health`, { headers: { host: 'evil.test' } }, response => {
      response.resume(); response.on('end', () => resolve(response.statusCode));
    });
  });
  assert.equal(wrongHostStatus, 403);
  let r = await fetch(`${base}/control/start`, { method: 'POST' }); assert.equal(r.status, 401); await r.text();
  r = await post(base, { model: 'other-model' }); assert.equal(r.status, 400); await r.text();
  const tracked = store.begin(true);
  assert.throws(() => store.stop(), /in_flight/);
  store.finish(tracked.runId, tracked.request, { ended_at: new Date().toISOString(), duration_ms: 0, status: 'transport_error' });
  assert.equal(store.stop().state, 'stopped');
});

test('setup and formalization have separate wall times and usage, with combined totals conserved', async t => {
  const { dir, store } = fixture(t);
  const run = store.start('appetizer', 'setup');
  assert.equal(run.state, 'running'); assert.ok(run.started_at);
  let s = store.summary(run.run_id);
  assert.equal(s.phases.setup.input_tokens, 0); assert.equal(s.phases.setup.cost_usd, 0);
  assert.equal(s.phases.formalization.state, 'not_started');
  // Local installation time counts even without a model request.
  await new Promise(resolve => setTimeout(resolve, 10));
  assert.ok(store.summary(run.run_id).phases.setup.wall_elapsed_seconds > 0);
  const setup = store.begin(false);
  assert.equal(setup.request.phase, 'setup');
  assert.throws(() => store.phase('formalization'), /in_flight_wait/);
  store.finish(run.run_id, setup.request, { ended_at: new Date().toISOString(), duration_ms: 1,
    generation_id: 'gen-setup', input_tokens: 100, output_tokens: 20, cost_usd: 0.01, status: 'completed' });
  store.phase('formalization');
  const intervals = store.readRun(run.run_id).phase_intervals;
  assert.equal(intervals[0].ended_at, intervals[1].started_at);
  store.phase('formalization'); // idempotent, no loss of measured time
  assert.equal(store.readRun(run.run_id).phase_intervals.length, 2);
  const proof = store.begin(true);
  assert.equal(proof.request.phase, 'formalization');
  store.finish(run.run_id, proof.request, { ended_at: new Date().toISOString(), duration_ms: 2,
    generation_id: 'gen-proof', input_tokens: 1000, output_tokens: 200, cost_usd: 0.03, status: 'completed' });
  await new Promise(resolve => setTimeout(resolve, 10));
  s = store.stop();
  assert.equal(s.phases.setup.input_tokens, 100); assert.equal(s.phases.setup.output_tokens, 20);
  assert.equal(s.phases.setup.cost_usd, 0.01);
  assert.equal(s.phases.formalization.input_tokens, 1000); assert.equal(s.phases.formalization.output_tokens, 200);
  assert.equal(s.phases.formalization.cost_usd, 0.03);
  assert.equal(s.input_tokens, 1100); assert.equal(s.output_tokens, 220); assert.equal(s.cost_usd, 0.04);
  assert.ok(Math.abs(s.wall_elapsed_seconds - s.phases.setup.wall_elapsed_seconds
    - s.phases.formalization.wall_elapsed_seconds) < 0.000001);
  const dirExport = join(dir, 'reports', run.run_id);
  assert.match(readFileSync(join(dirExport, 'phases.csv'), 'utf8'), /setup/);
  assert.match(readFileSync(join(dirExport, 'phases/formalization/requests.csv'), 'utf8'), /gen-proof/);
  assert.doesNotMatch(readFileSync(join(dirExport, 'phases/formalization/requests.csv'), 'utf8'), /gen-setup/);
  assert.equal(JSON.parse(readFileSync(join(dirExport, 'phases/setup/summary.json'), 'utf8')).cost_usd, 0.01);
});

test('late billing and duplicate generation IDs retain the original setup attribution across phase switches', async t => {
  const { store } = fixture(t); const run = store.start('appetizer', 'setup');
  const first = store.begin(false);
  store.finish(run.run_id, first.request, { ended_at: new Date().toISOString(), duration_ms: 1,
    generation_id: 'gen-phase-recover', status: 'interrupted' });
  store.phase('formalization');
  const duplicate = store.begin(false);
  store.finish(run.run_id, duplicate.request, { ended_at: new Date().toISOString(), duration_ms: 1,
    generation_id: 'gen-phase-recover', status: 'completed' });
  const upstream = await listen(t, http.createServer((req, res) => {
    res.setHeader('content-type', 'application/json');
    res.end(JSON.stringify({ data: { id: 'gen-phase-recover', native_tokens_prompt: 500,
      native_tokens_completion: 80, total_cost: 0.012 } }));
  }));
  await reconcile(store, run.run_id, async () => KEY, upstream);
  const s = store.stop();
  assert.equal(s.request_count, 2); assert.equal(s.unique_billing_records, 1);
  assert.equal(s.cost_usd, 0.012); assert.equal(s.phases.setup.cost_usd, 0.012);
  assert.equal(s.phases.formalization.cost_usd, 0);
  assert.equal(s.phases.setup.input_tokens, 500); assert.equal(s.phases.formalization.input_tokens, 0);
});

test('phase control endpoint validates phases and routes subsequent requests to the selected phase', async t => {
  const { store } = fixture(t);
  const base = await listen(t, createMeterServer({ store, apiKey: async () => KEY,
    controlToken: CONTROL, upstream: 'http://127.0.0.1:1', meterHash: 'test-hash' }));
  const control = (cmd, phase) => fetch(`${base}/control/${cmd}`, { method: 'POST',
    headers: { authorization: `Bearer ${CONTROL}`, 'x-experiment-phase': phase } });
  let r = await control('start', 'setup'); assert.equal(r.status, 200);
  const run = await r.json(); assert.equal(run.current_phase, 'setup');
  r = await control('phase', 'invalid'); assert.equal(r.status, 409);
  assert.equal((await r.json()).error, 'invalid_phase');
  r = await control('phase', 'formalization'); assert.equal(r.status, 200);
  assert.equal((await r.json()).current_phase, 'formalization');
  assert.throws(() => store.phase('not-a-phase'), /invalid_phase/);
  const row = store.begin(true);
  assert.equal(row.request.phase, 'formalization');
  store.finish(run.run_id, row.request, { status: 'transport_error', ended_at: new Date().toISOString(), duration_ms: 1 });
  store.stop(); assert.throws(() => store.phase('setup'), /stopped/);
});

test('phase attribution and boundaries survive restart without reclassifying historical untagged requests', t => {
  const { store } = fixture(t), run = store.start('appetizer', 'setup');
  const setup = store.begin(false);
  store.finish(run.run_id, setup.request, { ended_at: new Date().toISOString(), duration_ms: 1,
    input_tokens: 10, output_tokens: 2, cost_usd: 0.001, status: 'completed' });
  store.phase('formalization');
  const restored = new MetricsStore(store.root, store.exportRoot, {}, 'new-build-hash');
  const proof = restored.begin(false);
  assert.equal(proof.request.phase, 'formalization');
  restored.finish(run.run_id, proof.request, { ended_at: new Date().toISOString(), duration_ms: 1,
    input_tokens: 100, output_tokens: 20, cost_usd: 0.01, status: 'completed' });
  restored.append(run.run_id, { type: 'request_started', request_id: 'untagged-historical',
    started_at: new Date().toISOString(), ended_at: new Date().toISOString(), duration_ms: 0,
    input_tokens: 1, output_tokens: 1, cost_usd: 0, status: 'completed' });
  const s = restored.stop();
  assert.equal(s.phases.setup.input_tokens, 10); assert.equal(s.phases.formalization.input_tokens, 100);
  assert.equal(s.phases.unclassified.input_tokens, 1); assert.equal(s.phases.unclassified.wall_elapsed_seconds, null);
  assert.equal(s.input_tokens, 111); assert.equal(s.cost_usd, 0.011);
  assert.equal(s.phase_intervals.length, 2);
});

test('the local proxy credential is distinct from the upstream API credential', async t => {
  const LOCAL = 'synthetic-local-proxy-only-token';
  let forwarded = 0;
  const upstream = http.createServer((req, res) => {
    assert.equal(req.headers.authorization, `Bearer ${KEY}`);
    forwarded++;
    req.resume();
    res.setHeader('content-type', 'application/json');
    res.end(JSON.stringify({id:'gen-distinct-keys', usage:{prompt_tokens:1, completion_tokens:1, cost:0.001}, choices:[]}));
  });
  const upstreamUrl = await listen(t, upstream);
  const {store} = fixture(t); store.start('clean-auth-test');
  const meter = createMeterServer({store, apiKey:async()=>KEY, clientKey:async()=>LOCAL,
    controlToken:CONTROL, upstream:upstreamUrl, meterHash:'test-hash'});
  const url = await listen(t, meter);
  const send = token => fetch(`${url}/api/v1/chat/completions`, {method:'POST',
    headers:{authorization:`Bearer ${token}`,'content-type':'application/json'},
    body:JSON.stringify({model:MODEL,messages:[]})});
  assert.equal((await send(KEY)).status,401);
  assert.equal((await send(LOCAL)).status,200);
  assert.equal(forwarded,1);
});
