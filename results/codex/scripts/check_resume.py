#!/usr/bin/env python3
"""Check preservation and idle accounting on synthetic traces, without inference."""
import json
from pathlib import Path
import tempfile
from decimal import Decimal
from observe import summary
from run_trial import Driver

with tempfile.TemporaryDirectory() as tmp:
    case = Path(tmp)
    work = case / 'workspace'
    observer = case / 'observer'
    home = case / 'home'
    for p in (work / 'run', work / 'reports', observer, home / 'sessions'):
        p.mkdir(parents=True)
    (work / 'run/RESUME_AFTER_OPERATOR_001.txt').write_text('Retained operator clarification')
    (work / 'reports/STATUS.json').write_text('{"state":"claimed_complete_pending_audit"}')
    events = [{'unix': 1, 'type': 'thread_created', 'thread_id': 'original'},
              {'unix': 10, 'type': 'turn_started', 'turn_id': 'first'},
              {'unix': 20, 'type': 'turn_completed', 'turn_id': 'first'},
              {'unix': 10000, 'type': 'turn_started', 'turn_id': 'resumed'},
              {'unix': 10010, 'type': 'turn_completed', 'turn_id': 'resumed'}]
    (observer / 'lifecycle.jsonl').write_text('\n'.join(map(json.dumps, events)) + '\n')
    calls, supplied = [], []
    fake = Driver.__new__(Driver)
    fake.observer, fake.launch = observer, {'workspace': str(work)}
    def rpc(method, params):
        calls.append((method, params))
        return {'thread': {'id': 'original'}} if method == 'thread/resume' else {}
    fake.rpc, fake.send = rpc, lambda message: None
    fake.record = lambda *a, **k: None
    fake.turn = lambda text: supplied.append(text)
    fake.save_metrics = lambda **k: None
    fake.run(resume=True)
    assert [m for m, _ in calls] == ['initialize', 'thread/resume']
    assert calls[1][1]['threadId'] == 'original' and calls[1][1]['model'] == 'gpt-6.1-sol'
    assert supplied == ['Retained operator clarification'], 'Never rerun setup/start prompts on resume'
    (case / 'launch.json').write_text(json.dumps({'case': 'synthetic', 'codex_home': str(home)}))
    baseline = {'state': 'blocked', 'response_usage_records': 0,
        'tokens': {'input_tokens': 0, 'cached_input_tokens': 0, 'output_tokens': 0, 'reasoning_output_tokens': 0},
        'api_equivalent_usd': '0', 'active_seconds_excluding_between_turn_idle': 10}
    archive = observer / 'interventions/operator-clarification-001'
    archive.mkdir(parents=True)
    (archive / 'unassisted-measurement-baseline.json').write_text(json.dumps(baseline))
    out = summary(case)
    assert out['active_seconds_excluding_between_turn_idle'] == 20, 'Long clarification wait must stay excluded'
    assert out['assistance']['assisted_active_seconds'] == 10
    assert Decimal(out['assistance']['assisted_api_equivalent_usd']) == 0
print('PASS: same native thread, no setup replay, exact supplied clarification, idle-gap exclusion, assisted accounting')
