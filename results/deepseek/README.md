# DeepSeek formalization of Vershynin's HDP

Reproducibility release for two clean PDF-to-Lean experiments: the Appetizer
and Chapter 1 of Roman Vershynin's *High-Dimensional Probability*.

**Status:** model-reported complete mathematical coverage; operator-rerun Lean
builds and axiom checks passed. A full independent source-to-statement audit
remains pending for both projects. This release is intended to make that audit
possible, not to assert that compilation proves fidelity to the book.

## Quick start

Install Git, Python 3 and Lean's Elan toolchain manager using the
[Lean installation guide](https://leanprover-community.github.io/get_started.html).
No model account or API key is required to check the proofs.

```bash
git clone https://github.com/gspyrou1/hdp-formalization-deepseek.git
cd hdp-formalization-deepseek
python3 scripts/verify.py --fetch-cache
```

The verifier checks pinned versions and source hashes, downloads the Mathlib
build cache if requested, builds each project, and queries the axioms of its
public named definitions, lemmas and theorems (excluding historical Prop drafts).
It rejects unexpected axioms. Logs go to ignored `.verification/`. The first run
downloads Lean and dependencies and requires network access and several GB of disk.
See the [Mathlib project guide](https://leanprover-community.github.io/install/project).

To check one project manually:

```bash
cd appetizer  # or: cd chapter01
lake exe cache get
lake build HDP
lake env lean checks/Axioms.lean
lake env lean checks/Statements.lean
```

Use the committed `lean-toolchain` and `lake-manifest.json`; do not run
`lake update` for the pinned reproduction. Cache download is an optimization;
if unavailable, building dependencies from source may take substantially longer.

## Contents

- `appetizer/`: 8 final HDP modules plus their entry point.
- `chapter01/`: 13 final HDP modules plus their entry point.
- `reports/combined-experiment-report.pdf`: final combined report with reconciled metrics.
- `metrics/summary.json`, `metrics/runs.csv`, `metrics/runs/`: exact numeric exports.
- `reports/model-reports/`: original self-reviews, coverage inventories and attempt reports.
- `provenance/`: fixed protocol, exact continuation prompts, source hashes and
  earlier Chapter 1 source snapshots for progress inspection. These snapshots
  include incomplete work and are not the final build targets.
- `reports/release-verification.json`: checks performed on this exported package.

Both projects use the `HDP` namespace and are intentionally separate Lake
projects. Their final `.lean` files are copied byte for byte from the saved model
outputs. The release adds check scripts, documentation and a manifest-name
normalization; it does not repair the model's mathematics.

## Results at a glance

| Clean experiment | Active time including warm setup | Actual API cost | Attempts |
|---|---:|---:|---:|
| Appetizer | 48m 34.729s | $1.058237390 | 1 formalization attempt, 0 rescue continuations |
| Chapter 1 | 3h 1m 40.128s | $3.184093647 | 1 initial attempt + 4 human-prompted continuations |

Chapter 1's separate earlier setup calibration adds 33.207s and $0.005950590.
Formalization-only phase totals, tokens, per-attempt outcomes and limitations
are in the combined report and exact JSON. Setup here means warm protocol and
environment checks, not installation of the full upstream skill or toolchain.
The earlier nonclean Appetizer pilot is excluded. There is no Leanstral API trial
in this release.

All measured runs used `deepseek/deepseek-v4.1-flash-1017`, High reasoning, through
OpenRouter and `@deepseek-ai/dsh@0.2.1-rc.5`. Lean is pinned to
`leanprover/lean4:v4.29.0-rc3`; Mathlib is pinned to
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.

## Independent review

1. Build and inspect axiom output. `propext`, `Classical.choice` and `Quot.sound`
   are the only accepted nonempty axiom dependencies in this release check.
2. Inspect actual theorem signatures (`checks/Statements.lean`) and proofs,
   checking hypotheses, quantifiers, ranges, constants and conclusion strength
   against a lawful copy of the source identified in [SOURCE.md](SOURCE.md).
3. Check every coverage row, including exclusions and the roles of Mathlib reuse.
4. Record discrepancies separately; passing the compiler alone does not close
   the semantic review.

Specific review notes: Chapter 1's `OpenStatements.lean` retains historical
Prop-valued targets; these definitions are not proofs and are superseded by
the actual theorem declarations. The final `binomialMeasure` is defined as a
Bernoulli-sum law; equivalence to the separately retained PMF construction is
not claimed. The real-exponent `moment` definition inherits Mathlib's convention
for negative bases. The Appetizer required positive sample size and an explicit
constant 4 for its improved covering bound; see its self-review.

The original model reports contain provisional metric snapshots and earlier
coverage claims, some superseded by later continuations. Final reconciled
metrics in `metrics/` take precedence. An end-of-turn status of `completed`
does not by itself mean mathematical completion.

## Experimental limits

Only the assigned PDF, Lean core, pinned Mathlib and ordinary dependencies were
supplied for mathematics. Generic shell/PDF/compiler tools were allowed. The
agent was isolated from previous project formalizations and old Appetizer work;
pretraining exposure is not assessed. This used a custom generic protocol, not
the full released book-formalization skill. Chapter 1 was not a one-shot success.
The clean Appetizer encountered image attachment persistence failures and
continued through text/bounding-box extraction; Chapter 1 received an operational
viewer fix before its main formalization. Operator setup, idle UI recovery and
post-run checking are outside the reported active formalization time.

No credentials, raw session replay, hidden reasoning, private runtime homes,
vendored dependencies, or book PDFs are included. See [LICENSE-NOTICE.txt](LICENSE-NOTICE.txt).
