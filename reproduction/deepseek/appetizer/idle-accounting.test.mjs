import test from 'node:test';
import assert from 'node:assert/strict';
import { idleReport, nativeTimings, merge, subtract, primaryMeasurement } from './idle-accounting.mjs';

const base = 1700000000000;
const time = ms => new Date(base + ms).toISOString();
const event = (type, ms, data) => ({ type, time: base + ms, data });
const result = (callId, content = []) => ({ message: { role: 'tool',
  toolCallId: callId, source: { kind: 'tool', callId }, content } });
const run = { run_id: 'fixture', state: 'stopped', started_at: time(0), stopped_at: time(1000),
  phase_intervals: [{ phase: 'setup', started_at: time(0), ended_at: time(100) },
    { phase: 'formalization', started_at: time(100), ended_at: time(1000) }] };
const session = events => nativeTimings('session-test', events, 0, base + 1000);

test('overlapping interval union/subtraction preserves distinct gaps', () => {
  assert.deepEqual(merge([[0, 10], [5, 15], [20, 25]]), [[0, 15], [20, 25]]);
  assert.deepEqual(subtract([[0, 100]], [[20, 40], [30, 60], [80, 90]]), [[0, 20], [60, 80], [90, 100]]);
});

test('native approval waits are unioned, clipped to phases, and separated from actual tool work', () => {
  const s = session([
    event('turn/start', 0, { turn: 1 }), event('tool/call', 0, { callId: 'call-a', name: 'bash' }),
    event('approval/asked', 50, { id: 'approve-a', callId: 'call-a', reason: 'PRIVATE_REASON' }),
    event('approval/asked', 80, { id: 'approve-b', callId: 'call-a' }),
    event('approval/decided', 120, { id: 'approve-b', outcome: 'allowed-once' }),
    event('approval/decided', 150, { id: 'approve-a', outcome: 'allowed-once' }),
    event('tool/result', 200, result('call-a', [{ type: 'text', text: 'PRIVATE_RESULT' }])),
    event('turn/end', 200, { turn: 1 }),
  ]);
  const r = idleReport(run, [s], [], base + 1000);
  assert.equal(r.approval_wait_wall_seconds, 0.1);
  assert.equal(r.observed_blocking_human_wait_wall_seconds, 0.1);
  assert.equal(r.wall_excluding_observed_blocking_human_wait_seconds, 0.9);
  assert.equal(r.measured_elapsed_seconds, 0.1);
  assert.equal(r.excluded_idle_seconds, 0.9);
  assert.equal(r.phases.setup.measured_elapsed_seconds, 0.05);
  assert.equal(r.phases.formalization.measured_elapsed_seconds, 0.05);
  assert.equal(r.phases.setup.approval_wait_wall_seconds, 0.05);
  assert.equal(r.phases.formalization.approval_wait_wall_seconds, 0.05);
  assert.equal(r.between_turn_no_recorded_activity_wall_seconds, 0.8);
  assert.equal(r.approval_request_count, 2);
  assert.equal(JSON.stringify(r).includes('PRIVATE_'), false);
});

test('a wait overlapping parallel tool work and API calls is not all deducted from wall time', () => {
  const s = session([
    event('turn/start', 0, { turn: 1 }), event('tool/call', 0, { callId: 'call-a', name: 'bash' }),
    event('approval/asked', 50, { id: 'approve-a', callId: 'call-a' }),
    event('tool/call', 60, { callId: 'call-b', name: 'bash' }),
    event('tool/result', 120, result('call-b')),
    event('approval/decided', 150, { id: 'approve-a', outcome: 'rejected' }),
    event('tool/result', 200, result('call-a')), event('turn/end', 200, { turn: 1 }),
  ]);
  const r = idleReport(run, [s], [{ started_at: time(110), ended_at: time(140) }], base + 1000);
  assert.equal(r.approval_wait_wall_seconds, 0.1);
  assert.equal(r.observed_blocking_human_wait_wall_seconds, 0.02);
  assert.equal(r.measured_elapsed_seconds, 0.18);
});

test('pending approvals accrue until observation, and remain unresolved at an operator stop', () => {
  const s = session([event('turn/start', 0, { turn: 1 }),
    event('approval/asked', 100, { id: 'approve-a' })]);
  const liveRun = { ...run, state: 'running', stopped_at: null };
  const live = idleReport(liveRun, [s], [], base + 1000);
  assert.equal(live.pending_approval_requests, 1); assert.equal(live.approval_wait_wall_seconds, 0.9);
  const ended = idleReport(run, [s], [], base + 2000);
  assert.equal(ended.approval_wait_wall_seconds, 0.9);
  assert.equal(ended.waits[0].outcome, 'unresolved_at_stop');
});

test('question waits stop at tool settlement, not at a later answer to a continued question', () => {
  const s = session([event('turn/start', 0, { turn: 1 }),
    event('tool/call', 100, { callId: 'question-a', name: 'ask_user_question', arguments: 'PRIVATE_QUESTION' }),
    event('tool/result', 200, result('question-a')),
    event('user/message', 500, { message: { content: 'PRIVATE_ANSWER' } }),
    event('turn/end', 600, { turn: 1 })]);
  const r = idleReport(run, [s], [], base + 1000);
  assert.equal(r.foreground_user_question_wait_wall_seconds, 0.1);
  assert.equal(r.pending_foreground_questions, 0);
  assert.equal(JSON.stringify(r).includes('PRIVATE_'), false);
});

test('fork inheritance is excluded, missing native evidence stays unknown, and non-API tool time is not called idle', () => {
  const inherited = [event('approval/asked', 0, { id: 'parent-approval' })];
  const child = nativeTimings('child', [...inherited, event('turn/start', 50, { turn: 1 }),
    event('turn/end', 900, { turn: 1 })], 1, base + 1000);
  const r = idleReport(run, [child], [], base + 1000);
  assert.equal(r.approval_wait_wall_seconds, 0);
  assert.equal(r.outside_api_wall_seconds, 1);
  assert.equal(r.between_turn_no_recorded_activity_wall_seconds, 0.15);
  const unknown = idleReport(run, [], [], base + 1000, [{ error: 'read_failed' }]);
  assert.equal(unknown.approval_wait_wall_seconds, null);
  assert.equal(unknown.observed_blocking_human_wait_wall_seconds, null);
  assert.equal(unknown.coverage, 'incomplete');
  assert.equal(unknown.measured_elapsed_seconds, null);
});

test('the measured timer freezes during an unanswered approval and after turn completion', () => {
  const events = [event('turn/start', 0, { turn: 1 }),
    event('approval/asked', 100, { id: 'approval-pause' })];
  const liveRun = { ...run, state: 'running', stopped_at: null };
  const first = idleReport(liveRun, [nativeTimings('s', events, 0, base + 1000)], [], base + 1000);
  const later = idleReport(liveRun, [nativeTimings('s', events, 0, base + 5000)], [], base + 5000);
  assert.equal(first.measured_elapsed_seconds, 0.1); assert.equal(later.measured_elapsed_seconds, 0.1);
  assert.equal(later.wall_elapsed_seconds, 5);
  const doneEvents = [event('turn/start', 0, { turn: 1 }), event('turn/end', 200, { turn: 1 })];
  const done = idleReport(liveRun, [nativeTimings('s', doneEvents, 0, base + 5000)], [], base + 5000);
  assert.equal(done.measured_elapsed_seconds, 0.2);
  assert.equal(done.excluded_idle_seconds, 4.8);
});

test('local compilation and background jobs count even with no model requests', () => {
  const r = { ...run, stopped_at: time(2000), phase_intervals: [
    { phase: 'formalization', started_at: time(0), ended_at: time(2000) }] };
  const events = [event('turn/start', 0, { turn: 1 }),
    event('tool/call', 0, { callId: 'lean', name: 'bash' }),
    event('job/registered', 50, { jobId: 'build', startedAt: base + 50, toolCall: { rootCallId: 'lean' } }),
    event('tool/result', 100, result('lean')),
    event('turn/end', 100, { turn: 1 }),
    event('job/settled', 1500, { jobId: 'build', finishedAt: base + 1500 })];
  const report = idleReport(r, [nativeTimings('s', events, 0, base + 2000)], [], base + 2000);
  assert.equal(report.outside_api_wall_seconds, 2);
  assert.equal(report.measured_elapsed_seconds, 1.5);
  assert.equal(report.phases.formalization.measured_elapsed_seconds, 1.5);
});

test('primary report selects net elapsed time without changing token or billing totals', () => {
  const idle = idleReport(run, [session([event('turn/start', 0, { turn: 1 }),
    event('turn/end', 200, { turn: 1 })])], [], base + 1000);
  const api = { run_id: run.run_id, generated_at: time(300), wall_elapsed_seconds: 0.3,
    input_tokens: 1000, output_tokens: 200, cost_usd: 0.023,
    phases: { formalization: { input_tokens: 1000, output_tokens: 200, cost_usd: 0.023 } } };
  const report = primaryMeasurement(api, idle);
  assert.equal(report.primary_time_metric, 'measured_elapsed_seconds');
  assert.equal(report.measured_elapsed_seconds, 0.2); assert.equal(report.wall_elapsed_seconds, 1);
  assert.equal(report.input_tokens, 1000); assert.equal(report.output_tokens, 200); assert.equal(report.cost_usd, 0.023);
  assert.equal(report.phases.formalization.cost_usd, 0.023);
  assert.equal(report.api_accounting_snapshot_at, time(300));
  assert.throws(() => primaryMeasurement({ ...api, run_id: 'different' }, idle), /mismatch/);
});

test('native tool-result identities close tool spans and exclude hours after a completed turn', () => {
  const finish = 3000000, stopped = 21000000;
  const r = { ...run, stopped_at: time(stopped), phase_intervals: [
    { phase: 'formalization', started_at: time(0), ended_at: time(stopped) }] };
  const events = [event('turn/start', 0, { turn: 1 }),
    event('tool/call', 100, { callId: 'native-call-1', name: 'bash', arguments: 'PRIVATE_COMMAND' }),
    event('tool/result', 200, result('native-call-1')),
    event('tool/call', 300, { callId: 'native-call-2', name: 'bash' }),
    event('tool/result', 400, { message: { role: 'tool', source: { kind: 'tool', callId: 'native-call-2' }, content: [] } }),
    event('turn/end', finish, { turn: 1, reason: { kind: 'completed' } })];
  const s = nativeTimings('native-session', events, 0, base + stopped);
  assert.equal(s.open_tool_calls, 0); assert.equal(s.open_jobs, 0); assert.equal(s.open_turns, 0);
  const report = idleReport(r, [s], [], base + stopped);
  assert.equal(report.measured_elapsed_seconds, 3000);
  assert.equal(report.phases.formalization.measured_elapsed_seconds, 3000);
  assert.equal(report.excluded_idle_seconds, 18000);
  assert.equal(report.session_diagnostics[0].open_tool_calls, 0);
});
