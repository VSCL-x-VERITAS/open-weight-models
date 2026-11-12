// Derive timing from whitelisted native event metadata only. Never export
// commands, prompt/result text, question text, approval reasons or credentials.
const stamp = x => typeof x === 'number' && Number.isFinite(x) ? x : null;
const opaque = x => typeof x === 'string' && /^[A-Za-z0-9_.:-]{1,180}$/.test(x)
  && !/sk-or-|Bearer/i.test(x) ? x : null;
const iso = x => new Date(x).toISOString();
const seconds = intervals => Number((merge(intervals).reduce((s, [a, b]) => s + b - a, 0) / 1000).toFixed(6));

export function merge(intervals) {
  const result = [];
  for (const [a, b] of intervals.filter(([a, b]) => Number.isFinite(a) && Number.isFinite(b) && b > a)
    .sort((x, y) => x[0] - y[0])) {
    const previous = result.at(-1);
    if (previous && a <= previous[1]) previous[1] = Math.max(previous[1], b);
    else result.push([a, b]);
  }
  return result;
}
export function subtract(intervals, exclusions) {
  const cuts = merge(exclusions), result = [];
  for (const [a, b] of merge(intervals)) {
    let cursor = a;
    for (const [x, y] of cuts) {
      if (y <= cursor) continue;
      if (x >= b) break;
      if (x > cursor) result.push([cursor, Math.min(x, b)]);
      cursor = Math.max(cursor, y);
      if (cursor >= b) break;
    }
    if (cursor < b) result.push([cursor, b]);
  }
  return result;
}
const intersect = (values, windows) => merge(values.flatMap(([a, b]) => windows
  .map(([x, y]) => [Math.max(a, x), Math.min(b, y)])));

export function nativeTimings(sessionId, events, inherited = 0, until = Date.now()) {
  const approvals = new Map(), tools = new Map(), jobs = new Map(), turns = new Map();
  const allApprovals = [], allTools = [], allJobs = [], allTurns = [];
  let first = null, last = null;
  const close = (map, key, time, fields = {}) => {
    const row = map.get(key);
    if (!row) return;
    row.end = time; Object.assign(row, fields); map.delete(key);
  };
  for (const e of events.slice(inherited)) {
    const t = stamp(e.time); if (t === null) continue;
    first ??= t; last = t;
    const d = e.data ?? {};
    if (e.type === 'approval/asked') {
      const id = opaque(d.id); if (!id || approvals.has(id)) continue;
      const row = { session_id: sessionId, event_id: id, call_id: opaque(d.callId), start: t,
        end: null, kind: 'approval', outcome: 'pending' };
      approvals.set(id, row); allApprovals.push(row);
    } else if (e.type === 'approval/decided') {
      close(approvals, opaque(d.id), t, { outcome: ['allowed-once', 'rejected', 'cancelled', 'unavailable'].includes(d.outcome)
        ? d.outcome : 'unknown' });
    } else if (e.type === 'tool/call') {
      const id = opaque(d.callId); if (!id) continue;
      const row = { session_id: sessionId, event_id: id, call_id: id, start: t, end: null,
        kind: d.name === 'ask_user_question' ? 'foreground_user_question' : 'tool', outcome: 'pending' };
      tools.set(id, row); allTools.push(row);
    } else if (e.type === 'tool/result') {
      // Current native ToolResultMessage stores this identity in toolCallId
      // and source.callId, not message.callId. A missed match falsely leaves
      // a completed tool active indefinitely after the final turn.
      close(tools, opaque(d.message?.toolCallId ?? d.message?.source?.callId), t, { outcome: 'settled' });
    } else if (e.type === 'job/registered') {
      const id = opaque(d.jobId); if (!id) continue;
      const row = { session_id: sessionId, event_id: id, call_id: opaque(d.toolCall?.rootCallId),
        start: stamp(d.startedAt) ?? t, end: null, kind: 'job', outcome: 'pending' };
      jobs.set(id, row); allJobs.push(row);
    } else if (e.type === 'job/settled') {
      close(jobs, opaque(d.jobId), stamp(d.finishedAt) ?? t, { outcome: 'settled' });
    } else if (e.type === 'turn/start') {
      const key = String(d.turn);
      const row = { start: t, end: null }; turns.set(key, row); allTurns.push(row);
    } else if (e.type === 'turn/end') close(turns, String(d.turn), t);
  }
  const waits = [...allApprovals, ...allTools.filter(x => x.kind === 'foreground_user_question')];
  const range = row => [row.start, row.end ?? until];
  const waitRanges = waits.map(range);
  // The residual turn is conservatively treated as work. Waiting in one
  // parallel tool must not erase work in another tool, job or model call.
  const work = subtract(allTurns.map(range), waitRanges);
  for (const tool of allTools.filter(x => x.kind === 'tool')) {
    work.push(...subtract([range(tool)], allApprovals
      .filter(a => !a.call_id || a.call_id === tool.call_id).map(range)));
  }
  for (const job of allJobs) {
    work.push(...subtract([range(job)], allApprovals
      .filter(a => !a.call_id || a.call_id === job.call_id).map(range)));
  }
  return { session_id: sessionId, first_event_at: first, last_event_at: last,
    waits, work: merge(work), turns: allTurns.map(range), jobs: allJobs.map(range),
    tool_activity: allTools.map(range),
    pending_approvals: allApprovals.filter(x => x.end === null).length,
    open_tool_calls: tools.size, open_jobs: jobs.size, open_turns: turns.size,
    pending_foreground_questions: allTools.filter(x => x.kind === 'foreground_user_question' && x.end === null).length };
}

export function idleReport(run, sessions, requests, observed = Date.now(), failures = []) {
  const start = run.started_at ? Date.parse(run.started_at) : null;
  const end = Math.min(run.stopped_at ? Date.parse(run.stopped_at) : observed, observed);
  const windows = start === null ? [] : [[start, end]];
  const api = requests.map(r => [Date.parse(r.started_at), r.ended_at ? Date.parse(r.ended_at) : end]);
  const work = merge([...sessions.flatMap(x => x.work), ...api]);
  const activity = merge([...sessions.flatMap(x => [...x.turns, ...x.jobs, ...x.tool_activity]), ...api]);
  const waits = sessions.flatMap(x => x.waits);
  const approvals = waits.filter(x => x.kind === 'approval').map(x => [x.start, x.end ?? end]);
  const questions = waits.filter(x => x.kind === 'foreground_user_question').map(x => [x.start, x.end ?? end]);
  const humanWait = merge([...approvals, ...questions]);
  const blocked = subtract(humanWait, work);
  // Exclude the UNION: a pending wait and a durable-log gap may overlap.
  // Recorded local tool/job work remains counted even without an API call.
  const noActivity = subtract(windows, activity);
  const excluded = merge([...blocked, ...noActivity]);
  const healthy = failures.length === 0 && sessions.length > 0;
  function metrics(scope) {
    const windowSeconds = seconds(scope);
    const approvalSeconds = seconds(intersect(approvals, scope));
    const questionSeconds = seconds(intersect(questions, scope));
    const blockedSeconds = seconds(intersect(blocked, scope));
    return { wall_elapsed_seconds: windowSeconds,
      measured_elapsed_seconds: healthy ? seconds(subtract(scope, excluded)) : null,
      excluded_idle_seconds: healthy ? seconds(intersect(excluded, scope)) : null,
      approval_wait_wall_seconds: healthy ? approvalSeconds : null,
      foreground_user_question_wait_wall_seconds: healthy ? questionSeconds : null,
      observed_blocking_human_wait_wall_seconds: healthy ? blockedSeconds : null,
      wall_excluding_observed_blocking_human_wait_seconds: healthy
        ? Number((windowSeconds - blockedSeconds).toFixed(6)) : null,
      between_turn_no_recorded_activity_wall_seconds: healthy ? seconds(subtract(scope, activity)) : null,
      outside_api_wall_seconds: seconds(subtract(scope, api)),
    };
  }
  const phases = Object.fromEntries(['setup', 'formalization'].map(phase => [phase, metrics(
    (run.phase_intervals ?? []).filter(x => x.phase === phase && x.started_at)
      .map(x => [Date.parse(x.started_at), Math.min(x.ended_at ? Date.parse(x.ended_at) : end, end)]))]));
  const waitRows = waits.flatMap(row => intersect([[row.start, row.end ?? end]], windows).map(([a, b]) => ({
    kind: row.kind, session_id: row.session_id, event_id: row.event_id,
    started_at: iso(a), ended_at: (row.end === null || row.end > end) && run.state !== 'stopped' ? null : iso(b),
    measured_through: iso(b), duration_seconds: (b - a) / 1000,
    outcome: (row.end === null || row.end > end) && run.state === 'stopped' ? 'unresolved_at_stop' : row.outcome,
  })));
  return {
    schema_version: 2, run_id: run.run_id, state: run.state, generated_at: iso(observed),
    primary_time_metric: 'measured_elapsed_seconds',
    source: 'native Harness session timestamps, read through read-only persistence handles; API request ledger',
    coverage: healthy ? 'native_session_events_available' : 'incomplete',
    failed_session_reads: failures,
    session_ids: sessions.map(x => x.session_id),
    session_diagnostics: sessions.map(x => ({ session_id: x.session_id,
      open_tool_calls: x.open_tool_calls, open_jobs: x.open_jobs, open_turns: x.open_turns })),
    latest_native_event_at: sessions.length ? iso(Math.max(...sessions.map(x => x.last_event_at ?? 0))) : null,
    pending_approval_requests: healthy ? waitRows.filter(x => x.kind === 'approval' && x.ended_at === null).length : null,
    pending_foreground_questions: healthy ? waitRows.filter(x => x.kind === 'foreground_user_question' && x.ended_at === null).length : null,
    approval_request_count: waitRows.filter(x => x.kind === 'approval').length,
    ...metrics(windows), phases, waits: waitRows,
    definitions: {
      measured_elapsed: 'Primary experiment time: raw wall interval minus the union of observed blocking human waits and intervals without recorded agent turn, tool, job or API activity. Local compilation and concurrent productive work count. Applied separately to each phase.',
      approval_wait: 'Union of approval/asked to approval/decided intervals, including unanswered waits to the observation/stop time. Parallel work can overlap this measure.',
      foreground_question_wait: 'ask_user_question tool-call to tool-result only. A question that times out and continues is not treated as blocking thereafter.',
      blocking_human_wait: 'Observed approval/question waits excluding concurrent recorded API calls, tool/job work and residual active turns. Subtract this only when reporting wall time adjusted for human blocking.',
      between_turn_gap: 'No recorded agent turn, tool, job or API activity. Excluded from model/tool active time. Manual work outside Harness is not observed; its duration remains in raw wall time.',
      outside_api: 'Includes Lean compilation, other tools, waiting and gaps. It is not an idle-time measurement.',
      caveats: 'Durable logs can lag live state. Pending events survive a disconnected client or crashed host and cannot prove the host remains alive. Reads do not force a flush, change permissions or interrupt the agent. Adjusted wall time is not CPU time or proof-search time.',
    },
  };
}

export function primaryMeasurement(summary, idle) {
  if (summary.run_id !== idle.run_id) throw Error('timing_run_mismatch');
  const fields = timing => ({
    measured_elapsed_seconds: timing?.measured_elapsed_seconds ?? null,
    excluded_idle_seconds: timing?.excluded_idle_seconds ?? null,
  });
  return { ...summary,
    primary_time_metric: 'measured_elapsed_seconds',
    generated_at: idle.generated_at,
    wall_elapsed_seconds: idle.wall_elapsed_seconds,
    ...fields(idle),
    time_measurement_generated_at: idle.generated_at,
    api_accounting_snapshot_at: summary.generated_at,
    time_measurement_coverage: idle.coverage,
    time_measurement_definition: idle.definitions.measured_elapsed,
    phases: Object.fromEntries(Object.entries(summary.phases ?? {}).map(([name, phase]) => [name,
      { ...phase, wall_elapsed_seconds: idle.phases[name]?.wall_elapsed_seconds ?? phase.wall_elapsed_seconds,
        ...fields(idle.phases[name]) }])),
  };
}
