#!/usr/bin/env python3
"""Read native per-response token counters; never publish raw native rollouts."""
import datetime as dt
import json
from pathlib import Path
from decimal import Decimal

PRICE = {
    'model': 'gpt-6.1-sol', 'retrieved_date': '2026-11-03', 'currency': 'USD',
    'source': 'https://developers.openai.com/api/docs/models/gpt-6.1-sol',
    'standard_per_million': {'input': 2, 'cached_input': .1, 'output': 10},
    'long_context_input_threshold': 272000,
    'long_context_multipliers': {'input': 2, 'cached_input': 2, 'output': 1.5},
    'reasoning_is_subset_of_output': True,
    'estimate_not_invoice': True,
    'cache_write_note': 'Separate cache-write charges are not inferred from unreported fields. Estimate uses observed Codex cache reads; API cache behaviour may differ.',
}

def usage_records(home):
    records = []
    failures = []
    for path in sorted((home / 'sessions').rglob('*.jsonl')):
        cumulative_seen = set()
        session = None
        epoch = 0
        previous_total = -1
        for line_no, line in enumerate(path.read_text(errors='replace').splitlines(), 1):
            try:
                row = json.loads(line)
            except ValueError:
                continue  # Writer may currently have a partial terminal line.
            payload = row.get('payload', {})
            if row.get('type') == 'session_meta':
                session = payload.get('id')
            if row.get('type') != 'event_msg' or payload.get('type') != 'token_count':
                continue
            info = payload.get('info') or {}
            last, total = info.get('last_token_usage'), info.get('total_token_usage')
            if not isinstance(last, dict) or not isinstance(total, dict):
                continue
            total_number = total.get('total_tokens', 0)
            if total_number < previous_total:
                epoch += 1
            previous_total = total_number
            key = (epoch, json.dumps(total, sort_keys=True))
            if key in cumulative_seen:
                continue
            cumulative_seen.add(key)
            required = ('input_tokens', 'cached_input_tokens', 'output_tokens', 'reasoning_output_tokens')
            if not all(type(last.get(k)) is int for k in required):
                failures.append({'session_id': session, 'line': line_no, 'reason': 'missing per-response usage'})
                continue
            i, c, o, r = (last[k] for k in required)
            if min(i, c, o, r) < 0 or c > i or r > o:
                failures.append({'session_id': session, 'line': line_no, 'reason': 'inconsistent token subsets'})
                continue
            long = i > PRICE['long_context_input_threshold']
            cost = (Decimal(i - c) * (4 if long else 2) + Decimal(c) * Decimal('.2' if long else '.1') + Decimal(o) * (15 if long else 10)) / 1000000
            records.append({'session_id': session, 'native_line': line_no,
                            'timestamp': row.get('timestamp'), 'usage': last,
                            'long_context_pricing': long, 'api_equivalent_usd': str(cost)})
    return records, failures

def union_seconds(intervals):
    result = 0
    end = None
    for a, b in sorted(intervals):
        if end is None or a >= end:
            result += b - a
        elif b > end:
            result += b - end
        end = b if end is None else max(end, b)
    return result

def summary(case):
    launch = json.loads((case / 'launch.json').read_text())
    records, failures = usage_records(Path(launch['codex_home']))
    events_file = case / 'observer/lifecycle.jsonl'
    events = [json.loads(s) for s in events_file.read_text().splitlines()] if events_file.exists() else []
    starts, intervals = {}, []
    last_state = 'prepared'
    for row in events:
        if row['type'] == 'turn_started':
            starts[row['turn_id']] = row['unix']
        elif row['type'] in ('turn_completed', 'turn_failed', 'turn_interrupted'):
            start = starts.pop(row['turn_id'], None)
            if start is not None:
                intervals.append((start, row['unix']))
        elif row['type'] == 'state':
            last_state = row['state']
    now = dt.datetime.now(dt.timezone.utc).timestamp()
    intervals += [(a, now) for a in starts.values()]
    phases = case / 'workspace/reports/phase-events.jsonl'
    boundaries = [json.loads(s) for s in phases.read_text().splitlines()] if phases.exists() else []
    boundary = next((r['unix'] for r in boundaries if r['phase'] == 'formalization'), None)
    setup = [(a, min(b, boundary)) for a, b in intervals if a < boundary] if boundary else intervals
    formal = [(max(a, boundary), b) for a, b in intervals if b > boundary] if boundary else []
    totals = {k: sum(r['usage'].get(k, 0) for r in records) for k in ('input_tokens', 'cached_input_tokens', 'output_tokens', 'reasoning_output_tokens')}
    def phase_of(record):
        if not boundary or not record['timestamp']:
            return 'setup' if not boundary else 'unknown'
        timestamp = dt.datetime.fromisoformat(record['timestamp'].replace('Z', '+00:00')).timestamp()
        # Token completion can straddle a phase boundary; do not invent a split.
        return 'formalization' if timestamp >= boundary else 'setup'
    for r in records:
        r['phase_by_response_completion'] = phase_of(r)
    out = {'case': launch['case'], 'state': last_state, 'updated_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
           'model': PRICE['model'], 'reasoning_effort': 'high', 'response_usage_records': len(records),
           'tokens': totals, 'api_equivalent_usd': str(sum((Decimal(r['api_equivalent_usd']) for r in records), Decimal(0))),
           'active_seconds_excluding_between_turn_idle': union_seconds(intervals),
           'setup_active_seconds': union_seconds(setup), 'formalization_active_seconds': union_seconds(formal),
           'phase_usage': {phase: {k: sum(r['usage'].get(k, 0) for r in records if phase_of(r) == phase) for k in totals} for phase in ('setup', 'formalization', 'unknown')},
           'phase_usage_assignment': 'Native response-completion timestamp. Boundary-straddling response tokens cannot be split exactly.',
           'phase_boundary_unix': boundary, 'usage_anomalies': failures,
           'time_definition': 'Union of coordinator turn intervals, including model/tool execution; between-turn operator idle excluded. Approval policy never. Native provider backoff inside a live turn is included unless separately observed.',
           'cost_definition': 'Hypothetical standard API cost, per-response long-context tiers, cached reads as observed; reasoning already included in output. Not a subscription charge or API invoice.',
           'price_snapshot': PRICE,
           'records': records}
    # Preserve the original unassisted result and report additional native work
    # separately. The long gap while waiting for clarification is not active time.
    baseline_path = case / 'observer/interventions/operator-clarification-001/unassisted-measurement-baseline.json'
    if baseline_path.exists():
        baseline = json.loads(baseline_path.read_text())
        out['assistance'] = {
            'intervention_id': 'operator-clarification-001',
            'classification': 'operator-assisted continuation; original unassisted stop retained',
            'unassisted_baseline': {k: baseline[k] for k in ('response_usage_records','tokens','api_equivalent_usd','active_seconds_excluding_between_turn_idle')},
            'assisted_response_usage_records': len(records) - baseline['response_usage_records'],
            'assisted_tokens': {k: totals[k] - baseline['tokens'][k] for k in totals},
            'assisted_api_equivalent_usd': str(Decimal(out['api_equivalent_usd']) - Decimal(baseline['api_equivalent_usd'])),
            'assisted_active_seconds': out['active_seconds_excluding_between_turn_idle'] - baseline['active_seconds_excluding_between_turn_idle'],
            'operator_review_tokens_and_cost': None,
            'operator_review_note': 'Coordinating chat/research is outside the native trial meter; unavailable quantities are not inferred.'}
    return out

if __name__ == '__main__':
    import sys
    case = Path(sys.argv[1]).resolve()
    result = summary(case)
    destination = case / 'observer/measurement-summary.json'
    temporary = destination.with_suffix('.tmp')
    temporary.write_text(json.dumps(result, indent=2) + '\n')
    temporary.replace(destination)
    print(json.dumps({k: result[k] for k in ('case', 'state', 'response_usage_records', 'tokens', 'api_equivalent_usd', 'active_seconds_excluding_between_turn_idle')}))
