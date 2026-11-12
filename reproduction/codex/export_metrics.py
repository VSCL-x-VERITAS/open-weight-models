#!/usr/bin/env python3
"""Publish numeric snapshots and verify native model/counter provenance."""
import argparse
import hashlib
import json
from decimal import Decimal
from pathlib import Path
import sys

# Reuse the frozen accounting implementation with a caller-supplied run path.
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "results/codex/scripts"))
from observe import summary, usage_records

def export(case, destination):
    config = json.loads((case / 'launch.json').read_text())
    name = config['case']
    destination.mkdir(parents=True, exist_ok=True)
    home = Path(config['codex_home'])
    records, anomalies = usage_records(home)
    sessions = []
    for native in sorted((home / 'sessions').rglob('*.jsonl')):
        parsed = []
        for line in native.read_text().splitlines():
            try:
                parsed.append(json.loads(line))
            except ValueError:
                continue
        meta = next((r['payload'] for r in parsed if r.get('type') == 'session_meta'), {})
        contexts = [r['payload'] for r in parsed if r.get('type') == 'turn_context']
        observations = [{'model': c.get('model'), 'effort': c.get('effort'),
                         'approval_policy': c.get('approval_policy'),
                         'permission_profile': c.get('permission_profile')} for c in contexts]
        if not contexts or any(c.get('model') != 'gpt-6.1-sol' or c.get('effort') != 'high' for c in contexts):
            raise ValueError('Observed model/effort differs or is missing; do not price using Sol/High assumptions')
        counts = [r['payload']['info'] for r in parsed if r.get('type') == 'event_msg'
                  and r.get('payload', {}).get('type') == 'token_count' and r['payload'].get('info')]
        own = [r for r in records if r['session_id'] == meta.get('id')]
        latest = counts[-1]['total_token_usage'] if counts else {}
        observed = {k: sum(r['usage'].get(k, 0) for r in own) for k in latest}
        reset_seen = any(counts[i]['total_token_usage'].get('total_tokens', 0) < counts[i - 1]['total_token_usage'].get('total_tokens', 0) for i in range(1, len(counts)))
        reconciliation = 'counter_reset_requires_separate_review' if reset_seen else ('matches' if observed == latest else 'mismatch')
        # A growing file can advance between reads; this is a snapshot, not final
        # certification. Re-export after the worker has stopped for final checks.
        sessions.append({'session_id': meta.get('id'), 'source': meta.get('source'),
            'forked_from_id': meta.get('forked_from_id'), 'native_log_sha256_at_snapshot': hashlib.sha256(native.read_bytes()).hexdigest(),
            'observed_contexts': observations, 'latest_cumulative_tokens': latest,
            'sum_of_distinct_response_counters': observed, 'reconciliation': reconciliation,
            'task_events': [{'timestamp': r.get('timestamp'), 'type': r['payload']['type']}
                for r in parsed if r.get('type') == 'event_msg' and r.get('payload', {}).get('type') in ('task_started', 'task_complete', 'turn_aborted', 'context_compacted')]})
    destination.mkdir(parents=True, exist_ok=True)
    data = summary(case)
    data['phase_api_equivalent_usd'] = {phase: str(sum(
        (Decimal(r['api_equivalent_usd']) for r in data['records']
         if r['phase_by_response_completion'] == phase), Decimal(0)))
        for phase in ('setup', 'formalization', 'unknown')}
    data['native_verification'] = {'sessions': sessions,
        'interpretation': 'Native observations, not provider-signed evidence. Fresh fork metadata does not by itself certify semantic review independence. Running snapshots may be non-atomic.',
        'usage_anomalies': anomalies}
    (destination / f'{name}-measurement-snapshot.json').write_text(json.dumps(data, indent=2) + '\n')
    print(name, data['state'], data['response_usage_records'], 'responses;', len(sessions), 'native sessions')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("run", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    export(args.run.resolve(), args.output.resolve())
