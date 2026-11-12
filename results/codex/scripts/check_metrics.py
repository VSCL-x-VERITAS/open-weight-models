#!/usr/bin/env python3
"""Exercise accounting edge cases without spending model tokens."""
import json
from pathlib import Path
import tempfile
from decimal import Decimal
from observe import usage_records, union_seconds

def token_event(i, c, o, r, cumulative):
    return {'timestamp': '2026-11-03T10:00:00Z', 'type': 'event_msg', 'payload': {
        'type': 'token_count', 'info': {'last_token_usage': {'input_tokens': i,
        'cached_input_tokens': c, 'output_tokens': o, 'reasoning_output_tokens': r},
        'total_token_usage': {'total_tokens': cumulative}}}}

with tempfile.TemporaryDirectory() as tmp:
    home = Path(tmp)
    (home / 'sessions').mkdir()
    events = [{'type': 'session_meta', 'payload': {'id': 'test'}}]
    first = token_event(1000, 800, 100, 75, 1100)
    events += [first, first, token_event(300000, 280000, 1000, 900, 302100)]
    (home / 'sessions/test.jsonl').write_text('\n'.join(map(json.dumps, events)) + '\n')
    records, errors = usage_records(home)
    assert len(records) == 2 and not errors, 'Duplicate cumulative events must not inflate usage'
    assert Decimal(records[0]['api_equivalent_usd']) == Decimal('.00148')
    assert Decimal(records[1]['api_equivalent_usd']) == Decimal('.151'), 'Long context tiers must apply per response'
    # Reasoning is already included in output; adding it again is forbidden.
    assert records[0]['usage']['output_tokens'] == 100
    assert union_seconds([(0, 10), (5, 20), (25, 30)]) == 25
    (home / 'sessions/test.jsonl').write_text(json.dumps(token_event(10, 11, 5, 0, 15)))
    records, errors = usage_records(home)
    assert not records and len(errors) == 1, 'Inconsistent cache counts must remain visible'
print('PASS: deduplication, cached subsets, per-response long-context pricing, reasoning subsets, active interval union, anomaly reporting')
