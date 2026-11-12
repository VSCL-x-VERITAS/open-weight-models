# Clean PDF-to-Lean experiment

Work autonomously using only the assigned PDF, Lean and the pinned Mathlib
library (including its ordinary dependencies and Lean core). The workspace
starts with no chapter formalizations, inventories, theorem targets, proof
skeletons, solution hints, prior reviews or other model outputs. Generic editor,
shell, PDF reading/rendering and compilation tools are available. No web search,
other model, prior project files, user-global skills, external repositories,
historical sessions or imported workflow evidence are available for mathematics.
Do not seek them or attempt to circumvent the process boundary.

Read run/PROTOCOL.txt and the exact source PDF. Derive the mathematical inventory,
precise statements, formalization plan and Lean proofs yourself. Search the pinned
Mathlib and reuse matching results with explicit attribution. Keep Lean/Mathlib
pins fixed; do not run lake update or download additional mathematics.

Use tools/lean.sh for focused compiler checks and tools/lake.sh for builds.
Write chapter code under lean/HDP/ and import it from lean/HDP.lean. Preserve
source domains, hypotheses, quantifiers, constants and conclusion strength.
Do not substitute easier targets. No sorry, admit, custom theorem axioms, unsafe
proofs or target-valued assumptions count as completion. Inspect proof axioms.

This is a single DeepSeek agent experiment. Do not claim independent review from
self-review, another role label, a compiler check or a different session that was
never used. No Codex mathematical assistance or human proof suggestions are part
of the run. Complete source/statement self-review and kernel verification, and
label that review honestly. User interaction beyond the fixed launch prompts or
operational setup must be disclosed as intervention.

Continue all locally actionable work through the full source, including precise
exercises, body claims, definitions, equations, footnotes and Notes. Keep a
coverage inventory and durable checkpoints under reports/. A plan, partial draft,
green todo list or finished assistant turn is not completion. Report open items
honestly; never hide a hard result or narrow it to get a success label.

The operator controls measurement externally. Preserve the configured local
model endpoint. Do not start/stop/reset measurement or access private observer
state. Numeric exports under reports/metrics are observational metadata, not
mathematical input. Final metrics can remain provisional until the operator
stops and reconciles usage. Do not publish, push or open pull requests.
