# Codex: clean PDF-to-Lean formalization of HDP

This repository contains Codex-only formalizations of the Appetizer and Chapter 1
of Roman Vershynin's *High-Dimensional Probability*, plus experiment metrics and an
independent audit/comparison with DeepSeek. Final native Lean sources are exported
byte for byte. The original experiment workspaces were not changed by the audit.

**Audit verdict (3 November 2026): qualified completion.** Both fresh builds and
all-local-constant checks pass (186 Appetizer + 261 Chapter 1 constants). Fresh
source reviewers mapped 31 and 47 grouped comparison items and found no blocking
mismatch within the recorded amended finite-quantity scope. This does not certify
verbatim/unrestricted extended-valued completion of the original PDFs.

Variance additivity/exercises and Chebyshev retain finite-second-moment assumptions;
signed noninteger raw moments are explicitly domain-corrected. The source's informal
Notes sharpness is covered by the supplied precise worst-case dyadic contract.
A helper docstring overstates unrestricted real-integral meaning; its mathematical
source-facing result has the required finiteness hypothesis. No routine proving
resume is required for this scope. Broader infinite-variance coverage would require
additional work and review. Canonical Chapter PASS is not claimed.

See [the eight-page audit and comparison report](reports/codex-independent-audit-comparison.pdf),
[audit evidence](audit/audit-and-comparison.json), and [source-only code comparison](audit/reviews/code-comparison.json).
The original model completion records remain historical claims; the independent
operator verdict is separate. These are model reviews, not blinded human certification.

## Assisted continuation 001

Both original trials stopped with successful local Lean builds and an unresolved
source specification. Their exact stopping records and metrics were preserved
before any source clarification. The Appetizer used 19m54s active time and an
estimated $5.2570252 API-equivalent cost; Chapter 1 used 35m32s and $12.6732668.
Those times include the separately measured native setup turns.

The user then explicitly authorized the operator to independently review the
blockers, supply appropriate clarifications and resume both sessions. The operator
visually checked the original source passages, reviewed the relevant generated
definitions and consulted primary references. The retained amendments are in
`appetizer/experiment/operator-clarification-001/` and the corresponding Chapter 1
directory. They supply no Lean proofs and no prior project/experiment solutions.

- Appetizer Notes U17 now has a precise worst-case, universal-constant dyadic
  covering lower-bound target, derived from Carl–Pajor (1988), equation (2.14),
  for diameter-one coordinate cross-polytopes and the stated entropy range.
- Chapter 1 now explicitly uses positive integer raw moments for signed variables,
  positive real-order raw moments for nonnegative variables, and positive
  real-order absolute moments for signed variables. This is an operator-approved
  domain correction, not a claim that the original unrestricted wording was valid.

Both continuations reuse their original native session identities, proofs and
reviews. They run in parallel and require fresh independent Codex review of their
new contracts. Tool access restrictions, model, effort, compiler and dependencies
are unchanged. **These continuations are assisted; they must not be reported as
unassisted PDF-only completions.** Native assisted tokens, API-equivalent cost and
active time are reported separately from the frozen unassisted baselines. The
waiting interval is excluded. The coordinating chat/research is outside the native
meter; its unavailable tokens, time and cost are recorded as unknown.

## Experiment protocol

- Two independent workspaces and fresh model sessions; Chapter 1 cannot read the
  Appetizer trial output. Both begin with only `import Mathlib`.
- The worker receives the selected PDF, the tagged generic formalization skill,
  Lean, and official Mathlib dependencies. It receives no prior book-specific Lean
  code, source inventories, experiment reports or audit findings.
- Native Codex restricted-read permissions deny the rest of the filesystem and
  disable tool networking. Positive and negative access checks precede inference.
- Model: **GPT-6.1 Sol**, reasoning effort **High**, native ChatGPT sign-in. No model
  fallback, Claude consultation, external model or paid API key is configured.
- The skill's generator, independent faithfulness, verification and structure
  roles remain distinct. Actual native reviewer evidence must be retained.
- Worker turns continue automatically from persisted state when actionable work
  remains. Every continuation is recorded as an intervention, without added
  mathematical hints. A checkpoint or stopped turn is never completion.
- The complete supplied PDFs define scope, including mathematical exercises and
  operative notes. Each source item requires an explicit declaration mapping,
  review outcome, assumptions and status. Unresolved mismatches remain visible.

## Version pins and deliberate deviations

- Skill: [`formalization-collaboration` v8.1.70](https://github.com/VSCL-x-VERITAS/formalization-collaboration/tree/formalization-workflow-v8.1.70),
  commit `1fb46504020649465d98ef2533a926e8c1e4dbf4`.
- Lean: `leanprover/lean4:v4.29.0-rc3`.
- Mathlib: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.

The user explicitly selected **Codex only**. This skill release still requires a
Claude receipt for canonical source admission despite its optional-consultation
setting. That receipt will not be fabricated or relabeled. Codex-only source
review is a documented adaptation; canonical Claude admission and canonical
Chapter PASS must not be claimed without their actual evidence.

The full POSIX installer failed on macOS because its immutable-file checks require
Python's unavailable `os.listxattr` API. The four exact tagged skill packages were
installed using the standard Codex skill installer, with no upstream edits.
The full installer doctor did **not** pass. The actual native restricted-read
permission profile and Lean compilation were separately tested successfully.

This trial uses the full generic skill and independent Codex reviewers. The earlier
clean DeepSeek trial used a simpler generic protocol. That difference prevents a
strict model-only causal comparison and must be reported alongside results.

## Metrics

The observer retains native per-response input, cached-input, output and reasoning
token counters, including fresh reviewer sessions. Repeated cumulative events are
deduplicated. Reasoning is a subset of output and is not charged twice.

Setup and formalization are separate native turns, with an observer-recorded phase
boundary. Operator installation/preparation is separate from model setup. Active
time excludes between-turn operator idle; model and tool execution count. Provider
backoff inside a live turn remains included unless separately observable. A desktop
sleep or unobserved outage must be reported rather than silently subtracted.

API-equivalent cost is a **hypothetical estimate**, not an API invoice or a claim
about ChatGPT subscription billing. The dated price snapshot uses observed cache
reads and applies long-context tiers per response. API cache behaviour can differ;
unreported cache-write fees are not inferred. See `metrics/pricing.json`.

Raw native sessions, sign-in files, credentials, PDFs and dependency build caches
remain outside this repository. Public metrics and reviewer evidence must be
sanitized before publication.

## Verify Lean code independently

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan), clone
this repository, then run for each project:

```sh
cd appetizer
lake exe cache get
lake build
```

Repeat inside `chapter01`. The lockfiles pin dependencies. These commands compile the final native candidates. Run `lake env lean checks/AuditKernel.lean`
in each project for the all-local-constant check, or `python3 scripts/verify.py --fetch-cache`
from the repository root for both projects and source hashes. A successful build
alone does not establish correspondence with the book or source completeness.

The source PDFs are omitted. Their SHA-256 hashes and exact run instructions are
retained in `provenance/` and each project's `experiment/` directory.

## Local operator tools

`scripts/prepare.py` and `scripts/write_protocol.py` record the original local
preparation steps; they refer to this operator's paths and cached official Mathlib
dependencies. They are provenance, not a portable one-command bootstrap.
`scripts/run_trial.py` uses native Codex app-server, with fresh sessions and strict
permissions. `scripts/observe.py` exports accounting; `scripts/check_metrics.py`
checks deduplication, cache subsets, long-context pricing and interval accounting
without model calls. Run `scripts/status.py` on the original operator machine for
live status. The native sign-in remains accessible to Codex itself and denied to
model-generated commands.

## Independent audit records

`audit/` contains the independent source matrices, code comparison, original-input
hashes, fresh-build logs and kernel-check scripts. Absolute paths in JSON identify
the original operator machine: `.../codex-hdp-clean/CASE/workspace/lean/` maps to
`CASE/` here. DeepSeek references map to the separate DeepSeek repository.
`metrics/phase-summary.csv` separates native setup, unassisted formalization and
assisted formalization. Audit work and operator research are outside the native
trial meter and are not silently priced as zero.

The report can be regenerated with `python3 scripts/build_audit_report.py` after
installing ReportLab. Product source integrity is recorded in
`provenance/source-files.json` and `SHA256SUMS`. No source PDFs, sign-in files,
raw native sessions or dependency caches are distributed.
