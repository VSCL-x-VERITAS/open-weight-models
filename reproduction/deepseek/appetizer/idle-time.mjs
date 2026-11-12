#!/usr/bin/env node
import { existsSync, readFileSync, openSync, closeSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { spawn } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { atomicJson } from './metrics.mjs';
import { idleReport, nativeTimings, primaryMeasurement } from './idle-accounting.mjs';

const here = dirname(fileURLToPath(import.meta.url)), project = resolve(here, '../..');
const privateRoot = join(project, '.tools/deepseek-appetizer-clean/metrics');
const nodeModules = join(project, '.tools/deepseek-harness/node_modules/@deepseek-ai');
const workspace = join(here, 'workspace');
const watcherFile = join(privateRoot, 'idle-watcher.json');
const sourceHash = createHash('sha256').update(readFileSync(fileURLToPath(import.meta.url)))
  .update(readFileSync(join(here, 'idle-accounting.mjs'))).digest('hex');

async function nativeSessions() {
  const { Context } = await import(pathToFileURL(join(nodeModules, 'cordis/lib/index.js')));
  const Persistence = await import(pathToFileURL(join(nodeModules, 'dsh-session-persistence-jsonl/lib/index.js')));
  const ctx = new Context(), sessions = [], failures = [];
  try {
    await ctx.plugin(Persistence, { root: join(project, '.tools/deepseek-appetizer-clean/home/sessions'),
      compression: 'zstd', listConcurrency: 3 }).await();
    const list = await ctx.sessionPersistence.list();
    const ids = new Set(list.filter(x => x.header.cwd === workspace).map(x => x.header.id));
    let changed = true;
    while (changed) {
      changed = false;
      for (const x of list) if (ids.has(x.header.parentSession) && !ids.has(x.header.id)) { ids.add(x.header.id); changed = true; }
    }
    for (const x of list.filter(x => ids.has(x.header.id))) {
      let handle;
      try {
        handle = await ctx.sessionPersistence.open(x.header.id, 'read');
        const { events } = await handle.read();
        sessions.push(nativeTimings(x.header.id, events, handle.inheritedEventCount));
      } catch { failures.push({ session_id: x.header.id, error: 'native_session_read_failed' }); }
      finally { if (handle) await handle.close(); }
    }
  } finally { await ctx.fiber.dispose(); }
  return { sessions, failures };
}

function csv(file, columns, rows) {
  const text = [columns.join(','), ...rows.map(row => columns.map(key => `"${String(row[key] ?? '').replaceAll('"', '""')}"`).join(','))].join('\n') + '\n';
  // The snapshot JSON creates the export directory before this writes.
  return import('node:fs').then(fs => {
    const temporary = `${file}.${randomUUID()}.tmp`;
    fs.writeFileSync(temporary, text, { mode: 0o600 }); fs.renameSync(temporary, file);
  });
}

export async function snapshot() {
  const pointer = join(privateRoot, 'current.json');
  if (!existsSync(pointer)) return { state: 'not_started' };
  const id = JSON.parse(readFileSync(pointer, 'utf8')).run_id;
  if (!/^[0-9TZ-]+-[0-9a-f-]{36}$/.test(id)) throw Error('invalid_run_id');
  const dir = join(privateRoot, 'runs', id), run = JSON.parse(readFileSync(join(dir, 'run.json'), 'utf8'));
  const ledger = join(dir, 'events.jsonl'), requests = new Map();
  if (existsSync(ledger)) {
    const text = readFileSync(ledger, 'utf8');
    // Ignore an incomplete trailing write; do not repair or truncate the live ledger.
    for (const line of text.slice(0, text.lastIndexOf('\n') + 1).split('\n')) {
      if (!line.trim()) continue;
      const e = JSON.parse(line);
      requests.set(e.request_id, { ...requests.get(e.request_id), ...e });
    }
  }
  let native;
  try { native = await nativeSessions(); }
  catch { native = { sessions: [], failures: [{ error: 'native_session_inventory_failed' }] }; }
  const report = idleReport(run, native.sessions, [...requests.values()], Date.now(), native.failures);
  const out = join(workspace, 'reports/metrics', id);
  atomicJson(join(out, 'idle-summary.json'), report);
  atomicJson(join(workspace, 'reports/metrics/latest-idle-summary.json'), report);
  const apiSummaryFile = join(out, 'summary.json');
  if (existsSync(apiSummaryFile)) {
    const apiSummary = JSON.parse(readFileSync(apiSummaryFile, 'utf8'));
    const measurement = primaryMeasurement(apiSummary, report);
    atomicJson(join(out, 'measurement-summary.json'), measurement);
    atomicJson(join(workspace, 'reports/metrics/latest-measurement-summary.json'), measurement);
    await csv(join(out, 'measurement-phases.csv'), ['phase', 'measured_elapsed_seconds',
      'excluded_idle_seconds', 'wall_elapsed_seconds', 'input_tokens', 'output_tokens', 'cost_usd',
      'known_cost_usd', 'accounting_complete'], Object.entries(measurement.phases)
      .map(([phase, fields]) => ({ phase, ...fields })));
  }
  await csv(join(out, 'idle-waits.csv'), ['kind', 'session_id', 'event_id', 'started_at', 'ended_at',
    'measured_through', 'duration_seconds', 'outcome'], report.waits);
  await csv(join(out, 'idle-phases.csv'), ['phase', 'measured_elapsed_seconds', 'excluded_idle_seconds',
    'wall_elapsed_seconds', 'approval_wait_wall_seconds',
    'foreground_user_question_wait_wall_seconds', 'observed_blocking_human_wait_wall_seconds',
    'wall_excluding_observed_blocking_human_wait_seconds', 'between_turn_no_recorded_activity_wall_seconds'],
    Object.entries(report.phases).map(([phase, fields]) => ({ phase, ...fields })));
  return report;
}

export function startIdleWatcher() {
    if (existsSync(watcherFile)) {
      const state = JSON.parse(readFileSync(watcherFile, 'utf8'));
      let alive = false; try { process.kill(state.pid, 0); alive = true; } catch {}
      if (alive && state.source_sha256 === sourceHash) return 'already_running';
      if (alive) throw Error('different_idle_collector_running');
    }
    const log = openSync(join(privateRoot, 'idle-watcher.log'), 'a', 0o600);
    const env = { ...process.env }; delete env.OPENROUTER_API_KEY;
    const child = spawn(process.execPath, [fileURLToPath(import.meta.url), 'collect'], {
      cwd: here, env, detached: true, stdio: ['ignore', log, log],
    });
    closeSync(log); child.unref();
    atomicJson(watcherFile, { pid: child.pid, started_at: new Date().toISOString(), source_sha256: sourceHash });
    return 'started';
}

async function main() {
  const command = process.argv[2] ?? 'status';
  if (command === 'watch') {
    console.log(`Read-only idle-time collector: ${startIdleWatcher()}; refresh interval 15 seconds.`);
  } else if (command === 'collect') {
    while (true) {
      let state;
      try { state = (await snapshot()).state; } catch { console.error('Idle snapshot failed; no agent or metric state was changed.'); }
      if (state === 'stopped' || state === 'not_started') break;
      await new Promise(resolve => setTimeout(resolve, 15000));
    }
  } else if (command === 'status') console.log(JSON.stringify(await snapshot(), null, 2));
  else throw Error('unknown_idle_command');
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch(() => { console.error('Idle-time logging command failed. No raw session content was printed.'); process.exitCode = 1; });
}
