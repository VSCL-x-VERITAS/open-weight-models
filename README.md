# HDP PDF-to-Lean experiments with DeepSeek and Codex

This repository contains the four Lean projects produced from the Appetizer and
Chapter 1 of Roman Vershynin's *High-Dimensional Probability*. Each run began
with the assigned PDF, a fresh Lean project, and pinned Mathlib. The agents had
no access to VSCL or earlier formalizations. The two workflows used different
review procedures. Codex received two documented source clarifications after its
initial runs stopped, one for each chapter-sized unit.

| Run | Lean outputs, prompts, and metrics | Correspondence audit |
| --- | --- | --- |
| DeepSeek V4.1 Flash 1017, High | [Frozen release](results/deepseek/) | [Audit report](audit/deepseek-correspondence/report.pdf) |
| Codex with GPT-6.1 Sol, High | [Frozen release](results/codex/) | [Audit and comparison](results/codex/reports/codex-independent-audit-comparison.pdf) |

Both releases include their original checks and SHA-256 manifests. Builds check
Lean validity. The audits separately assess coverage and correspondence with
the source, including omissions and restrictions on assumptions.

## Verify the results

Install elan and Python 3.10 or later. From the repository root, run:

```sh
(cd results/deepseek && shasum -a 256 -c SHA256SUMS)
(cd results/codex && shasum -a 256 -c SHA256SUMS)
python3 results/deepseek/scripts/verify.py --fetch-cache
python3 results/codex/scripts/verify.py --fetch-cache
python3 reproduction/verify_metrics.py
```

The commands require network access for the pinned Lean toolchain and
dependencies. They require no model account, API key, or source PDFs.

## Reproduce the procedure

See [the rerun guide](reproduction/README.md) for clean workspace preparation,
phase boundaries, operator prompts, isolation checks, and metrics collection.
[Source identification](results/deepseek/SOURCE.md) gives the exact PDF hashes.
A rerun requires those inputs and access to the named hosted models. Outputs,
stopping points, timings, and API cache behaviour can vary between runs.

The original release snapshots are DeepSeek
`11c5bcf20f1e91b501c96fce3038ba4ad39dafc6` and Codex
`3497476005734d39bd0b2eab0ce1a6327087af91`. Source PDFs and private session
transcripts are omitted. Prompts, interventions, usage evidence, and the audit
records are included.
