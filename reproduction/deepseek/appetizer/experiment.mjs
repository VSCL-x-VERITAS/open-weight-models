#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { existsSync, openSync, closeSync, readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { randomBytes } from 'node:crypto';
import { atomicJson, createMeterServer, MetricsStore, SERVICE, sourceHash } from './metrics.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const project = resolve(here, '../..');
const root = join(project, '.tools/deepseek-appetizer-clean/metrics');
const stateFile = join(root, 'proxy.json');
const credentialsFile = join(project, '.tools/deepseek-appetizer/home/.credentials.yaml');
const manifestFile = join(here, 'workspace/run/experiment.json');
const exportRoot = join(here, 'workspace/reports/metrics');
const meterHash = sourceHash(join(here, 'metrics.mjs'));
const PORT = 3087;
const [command = 'help', ...args] = process.argv.slice(2);
let label = args[0], initialPhase = 'formalization';
if (command === 'start') {
  label = undefined;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--phase') initialPhase = args[++i];
    else if (!label && !args[i].startsWith('-')) label = args[i];
    else { console.error('Usage: ./experiment.sh start [label] [--phase setup|formalization]'); process.exit(1); }
  }
}

async function key() {
  const { parseCredentialsDocument } = await import(pathToFileURL(join(project,
    '.tools/deepseek-harness/node_modules/@deepseek-ai/dsh-credentials-local/lib/index.js')));
  const value = parseCredentialsDocument(readFileSync(credentialsFile, 'utf8'), credentialsFile)
    .refs.get('OPENROUTER_API_KEY');
  if (!value) throw new Error('missing_credential');
  return value;
}
async function clientKey() {
  const { parseCredentialsDocument } = await import(pathToFileURL(join(project,
    '.tools/deepseek-harness/node_modules/@deepseek-ai/dsh-credentials-local/lib/index.js')));
  const file = join(project, '.tools/deepseek-appetizer-clean/home/.credentials.yaml');
  return parseCredentialsDocument(readFileSync(file, 'utf8'), file).refs.get('OPENROUTER_API_KEY');
}
function store() {
  return new MetricsStore(root, exportRoot, JSON.parse(readFileSync(manifestFile, 'utf8')), meterHash);
}
async function health() {
  try {
    const response = await fetch(`http://127.0.0.1:${PORT}/health`, { signal: AbortSignal.timeout(1000) });
    return response.ok ? await response.json() : null;
  } catch { return null; }
}
async function ensure() {
  const existing = await health();
  if (existing) {
    if (existing.service !== SERVICE || existing.meter_sha256 !== meterHash || !existsSync(stateFile)) {
      throw new Error('Port 3087 has another service or an older meter. No process was stopped.');
    }
    return;
  }
  store(); // creates only the private storage directory
  const log = openSync(join(root, 'proxy.log'), 'a', 0o600);
  const env = { ...process.env }; delete env.OPENROUTER_API_KEY;
  const child = spawn(process.execPath, [fileURLToPath(import.meta.url), 'serve'], {
    cwd: here, env, detached: true, stdio: ['ignore', log, log],
  });
  closeSync(log);
  child.unref();
  for (let i = 0; i < 40; i++) {
    await new Promise(resolve => setTimeout(resolve, 100));
    const value = await health();
    if (value?.service === SERVICE && value.meter_sha256 === meterHash && existsSync(stateFile)) return;
  }
  throw new Error('Meter did not start. Check its private proxy.log; port 3087 may be occupied.');
}

try {
  if (command === 'serve') {
    process.umask(0o077);
    const controlToken = randomBytes(32).toString('hex');
    const server = createMeterServer({ store: store(), apiKey: key, clientKey, controlToken, meterHash });
    server.requestTimeout = 0; // Long reasoning responses must not time out locally.
    server.on('error', () => { console.error('Meter listener failed.'); process.exit(1); });
    server.listen(PORT, '127.0.0.1', () => {
      atomicJson(stateFile, { service: SERVICE, pid: process.pid, port: PORT, control_token: controlToken, meter_sha256: meterHash });
      console.log('Appetizer meter listening on 127.0.0.1:3087. No model request made.');
    });
  } else if (command === 'ensure') {
    await ensure(); console.log('Appetizer API meter ready on 127.0.0.1:3087.');
  } else if (command === 'idle') {
    const { snapshot } = await import('./idle-time.mjs');
    console.log(JSON.stringify(await snapshot(), null, 2));
  } else if (['start', 'phase', 'status', 'stop', 'reconcile'].includes(command)) {
    await ensure();
    const state = JSON.parse(readFileSync(stateFile, 'utf8'));
    const headers = { authorization: `Bearer ${state.control_token}` };
    if (command === 'start' && label) headers['x-experiment-label'] = label;
    if (command === 'start') headers['x-experiment-phase'] = initialPhase ?? '';
    if (command === 'phase') headers['x-experiment-phase'] = label ?? '';
    const response = await fetch(`http://127.0.0.1:${PORT}/control/${command}`, {
      method: 'POST', headers,
    });
    const data = await response.json();
    if (!response.ok) throw new Error(data.error);
    // This companion reader never changes or restarts the running API meter.
    // Keep original request accounting intact if a native-log read fails.
    try {
      const { snapshot, startIdleWatcher } = await import('./idle-time.mjs');
      if (command === 'start') data.idle_collector = startIdleWatcher();
      if (['status', 'stop', 'reconcile'].includes(command)) {
        const idle = await snapshot();
        const { primaryMeasurement } = await import('./idle-accounting.mjs');
        const summary = command === 'reconcile' ? data.summary : data;
        const measured = primaryMeasurement(summary, idle);
        if (command === 'reconcile') data.summary = measured;
        else Object.assign(data, measured);
        data.idle_time = idle;
      }
    } catch {
      data.primary_time_metric = 'measured_elapsed_seconds';
      data.measured_elapsed_seconds = null;
      data.idle_time = { coverage: 'native_idle_logging_unavailable' };
    }
    console.log(JSON.stringify(data, null, 2));
  } else if (command === 'export') {
    // Offline export works even after the server or machine was restarted.
    const s = store(), id = label ?? s.current();
    let report = s.export(id);
    if (id) {
      try {
        const { primaryMeasurement } = await import('./idle-accounting.mjs');
        const idle = id === s.current() ? await (await import('./idle-time.mjs')).snapshot()
          : JSON.parse(readFileSync(join(exportRoot, id, 'idle-summary.json'), 'utf8'));
        report = primaryMeasurement(report, idle);
      } catch {
        report.primary_time_metric = 'measured_elapsed_seconds'; report.measured_elapsed_seconds = null;
        report.time_measurement_coverage = 'native_idle_logging_unavailable';
      }
    }
    console.log(JSON.stringify(report, null, 2));
  } else {
    console.log('Usage: ./experiment.sh start [label] [--phase setup|formalization]');
    console.log('       ./experiment.sh phase setup|formalization');
    console.log('       ./experiment.sh status | idle | stop | reconcile | export [run-id]');
    console.log('setup starts timing immediately, including local installation; the default formalization start waits for the first API request.');
    console.log('Phase switches start timing immediately and require no API request in flight. stop records no mathematical completion claim.');
    console.log('Primary reported time is measured_elapsed_seconds, excluding observed idle/wait time; raw wall time is retained separately.');
    if (command !== 'help') process.exitCode = 1;
  }
} catch (error) {
  // Whitelist our own control codes; never echo credential/parser/fetch errors.
  const known = new Set(['start_experiment_before_sending_prompt', 'experiment_is_stopped',
    'run_already_armed_or_running', 'invalid_label', 'invalid_phase', 'no_experiment',
    'requests_in_flight_stop_harness_generation_first', 'requests_in_flight_wait_before_switching_phase']);
  if (known.has(error.message)) console.error(`Experiment command failed: ${error.message}`);
  else console.error('Experiment command failed. Check the private meter log and whether port 3087 is available.');
  process.exitCode = 1;
}
