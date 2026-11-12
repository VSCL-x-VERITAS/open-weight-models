#!/usr/bin/env python3
"""Print current native trial state and refresh numeric metrics."""
import json
from observe import summary
from prepare import TRIALS

for name in ('appetizer', 'chapter01'):
    case = TRIALS / name
    if not (case / 'launch.json').exists():
        print(f'{name}: not prepared')
        continue
    data = summary(case)
    temp = case / 'observer/measurement-summary.tmp'
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(case / 'observer/measurement-summary.json')
    print(json.dumps({k: data[k] for k in ('case', 'state', 'response_usage_records', 'tokens', 'active_seconds_excluding_between_turn_idle', 'api_equivalent_usd')}))
