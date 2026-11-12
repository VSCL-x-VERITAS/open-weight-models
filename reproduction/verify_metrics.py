#!/usr/bin/env python3
"""Reconcile the shipped per-request and per-response metrics with the release totals."""
from decimal import Decimal
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(path):
    return json.loads(path.read_text(), parse_float=Decimal)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def deepseek():
    snapshots = ROOT / "results/deepseek/metrics/runs"
    evidence = ROOT / "reproduction/deepseek/receipt-evidence"
    pairs = {
        "input_tokens": "input_tokens",
        "output_tokens": "output_tokens",
        "reported_cached_input_tokens": "cached_input_tokens",
        "reported_reasoning_tokens": "reasoning_tokens",
        "cost_usd": "cost_usd",
    }
    published = load(ROOT / "results/deepseek/metrics/summary.json")
    cases = {"appetizer": [], "chapter01": []}
    for file in sorted(snapshots.glob("*.json")):
        data = load(file)
        rows = load(evidence / file.name)["records"]
        require(len(rows) == data["request_count"], f"{file.name}: request count")
        for key, field in pairs.items():
            require(sum(row[field] or 0 for row in rows) == data[key], f"{file.name}: {key}")
        if data["classification"] != "SETUP_CALIBRATION_ONLY":
            cases[data["project"]].append(data)
    for case, runs in cases.items():
        field = "all_measured_phases" if case == "appetizer" else "main_attempt_and_continuations"
        total = published[case][field]
        for key in (*pairs, "request_count", "measured_elapsed_seconds"):
            require(sum(run[key] for run in runs) == total[key], f"DeepSeek {case}: {key}")
        print(f"DeepSeek {case}: {total['request_count']} requests reconcile")


def codex():
    for case in ("appetizer", "chapter01"):
        data = load(ROOT / f"results/codex/metrics/{case}-measurement-snapshot.json")
        rows = data["records"]
        require(len(rows) == data["response_usage_records"], f"Codex {case}: response count")
        for key, expected in data["tokens"].items():
            require(sum(row["usage"].get(key, 0) for row in rows) == expected, f"Codex {case}: {key}")
        total = sum(Decimal(row["api_equivalent_usd"]) for row in rows)
        require(total == Decimal(data["api_equivalent_usd"]), f"Codex {case}: cost")
        print(f"Codex {case}: {len(rows)} responses reconcile")


if __name__ == "__main__":
    deepseek()
    codex()
