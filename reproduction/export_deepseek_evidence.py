#!/usr/bin/env python3
"""Export numeric receipt evidence from the original operator workspaces."""
import argparse
import json
from pathlib import Path

NUMERIC = ("input_tokens", "output_tokens", "cached_input_tokens",
           "reasoning_tokens", "cache_write_tokens", "cost_usd",
           "duration_ms", "time_to_first_byte_ms", "http_status")


def export(operator_output, release):
    original = release / "results/deepseek/metrics/runs"
    destination = release / "reproduction/deepseek/receipt-evidence"
    destination.mkdir(exist_ok=True)
    for file in sorted(original.glob("*.json")):
        summary = json.loads(file.read_text())
        case = summary["project"]
        run = summary["run_id"]
        path = (operator_output / f"deepseek-{case}-clean-api/workspace/reports/metrics"
                / run / "requests.json")
        rows = json.loads(path.read_text())
        records = []
        for row in rows:
            record = {}
            for k in NUMERIC:
                value = row.get(k)
                if value is not None and type(value) not in (int, float):
                    raise ValueError(f"Unexpected nonnumeric {k} in {run}")
                record[k] = value
            phase = row.get("phase")
            record["phase"] = phase if phase in ("setup", "formalization") else None
            records.append(record)
        evidence = {"run": run, "case": case, "records": records}
        (destination / file.name).write_text(json.dumps(evidence, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operator_output", type=Path)
    args = parser.parse_args()
    export(args.operator_output, Path(__file__).resolve().parents[1])
