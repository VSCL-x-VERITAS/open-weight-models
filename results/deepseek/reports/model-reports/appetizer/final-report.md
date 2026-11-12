# Final report: Appetizer PDF-to-Lean formalization

## Scope

Source: `source/Appetizer.pdf` (4 pages), the Appetizer section on Maurey's
empirical method. The complete mathematical inventory, including numbered
theorems, exercises, the footnote, displayed identities and proof claims, is in
`reports/INVENTORY.md`.

## Result summary

All numbered results, exercises and the sharpness remark in the source are
formalized in Lean 4 with the pinned Mathlib.

- `HDP.caratheodory` — Theorem 0.0.1.
- `HDP.caratheodory_bound_sharp` — sharpness remark after Theorem 0.0.1
  (the standard `(n+1)`-vertex simplex needs all `n+1` vertices).
- `HDP.approximate_caratheodory` — Theorem 0.0.2, including the general
  `diam(T)/√k` form of footnote 1.
- `HDP.integral_norm_sq_sum_of_indep_mean_zero` — Exercise 0.0.3(a).
- `HDP.variance_identity_vector` — Exercise 0.0.3(b).
- `HDP.covering_polytope` — Corollary 0.0.4.
- `HDP.sum_choose_bounds` — Exercise 0.0.5, all three inequalities.
- `HDP.improved_covering` — Exercise 0.0.6 with the explicit absolute
  constant `C = 4`, i.e. `(4 + 4 ε² N)^⌈1/ε²⌉` balls suffice.
- `HDP.IsConvexCombination`, `HDP.mem_convexHull_iff_exists_convexCombination`,
  `HDP.diameter`, `HDP.DiameterLe` — definitions (0.1) and `conv(T)`.

Proof intermediates (translation, probabilistic mean, variance computation,
existence of a realization, center-set cardinalities) are used as Lean lemmas
and are tracked in `reports/INVENTORY.md`.

## Reused Mathlib results (with source roles)

- `Caratheodory.minCardFinsetOfMemConvexHull`,
  `Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull`,
  `AffineIndependent.card_le_finrank_succ`: finite-dimensional Carathéodory
  argument and the `n+1` cardinal bound in Theorem 0.0.1.
- `convexHull_eq`/`mem_convexHull_iff_exists_fintype`: identification of the
  source's `conv(T)` with Mathlib's `convexHull`.
- `PMF.ofFintype`, `PMF.toMeasure`, `Measure.pi`, `Measure.pi_map_eval`,
  `MeasureTheory.measurePreserving_eval`: finite sampling model for the
  empirical method and marginal calculations.
- `IndepFun.variance_sum`, `variance_of_integral_eq_zero`: scalar variance
  identity used coordinate-wise for Exercise 0.0.3(a) and Theorem 0.0.2.
- `EuclideanSpace.norm_sq_eq`, `PiLp.norm_apply_le`: coordinate expansion of
  the Euclidean norm.
- `Stirling.le_factorial_stirling`, `Nat.choose_le_pow_div`: single-term
  binomial estimate used in Exercise 0.0.6.
- `Sym.card_sym_eq_choose`, `Finset.sym`: unordered multisets of vertices and
  the `C(N+k−1,k)` count in Exercise 0.0.6.
- `Metric.dist_le_diam_of_mem`: conversion of the diameter hypothesis to
  pairwise distance bounds.

## Self-review of statements (not an independent audit)

I checked each Lean statement against the source text myself. This is
self-review only; no independent reviewer or separate verification session was
used. Points deliberately recorded:

- The source says "every integer `k`" in Theorem 0.0.2. The displayed quantity
  uses `1/k` and `1/√k`, so the formal statement requires `0 < k`; `k = 0` is
  not a meaningful instance of the source formula.
- Corollary 0.0.4 is stated for a vertex finset `s` with `s.card = N`; the
  source's "polytope with `N` vertices" is represented by its vertex set and
  convex hull. `Metric.diam` is accompanied by `Bornology.IsBounded`, which is
  part of the source's "diameter bounded" condition.
- Exercise 0.0.3(a) is formalized for `EuclideanSpace ℝ (Fin n)` (the source's
  `ℝⁿ`), with independence as `iIndepFun` and zero means as `∫ W = 0`.
- Exercise 0.0.6 allows any absolute constant; the formal version fixes the
  explicit constant `4`, which satisfies the source's `(C + C ε² N)` form.

## Verification evidence

Build command:

```
tools/lake.sh build HDP
```

Result: `Build completed successfully` (all HDP modules).

Axiom inspection (`tools/lean.sh reports/CHECK_AXIOMS.lean`) reports for every main
theorem exactly the standard Lean axioms `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, `admit`, custom axiom, unsafe proof or target-valued
assumption occurs. A textual search of `lean/HDP` and `lean/HDP.lean` for
`sorry`, `admit`, `axiom`, `unsafe` returned no hits.

## Open items

None. All mathematical items inventoried in `reports/INVENTORY.md` are
formalized. This is a coverage statement, not an independent semantic audit;
the statement self-review above is the author's own review.


## Available metric snapshot (provisional)

The latest metric export available while writing this report was
`reports/metrics/latest-summary.json`, generated at
`2026-11-02T00:11:46.889Z` (run still `running`, `accounting_complete: false`).
It reports `request_count: 347`, `known_input_tokens: 78109471`,
`known_output_tokens: 211464`, `reported_reasoning_tokens: 201242`,
`known_cost_usd: 1.029308046`, and one request with missing usage records. This
snapshot predates much of the formalization work and is not reconciled; final
metrics remain provisional until the operator stops and reconciles usage. These
numbers are observational metadata only and were not used as mathematical input.

## Independence / interventions

No web search, other model, prior formalization, external repository or
user-global skill was used for mathematics. No Codex or human proof suggestions
were used. The only user turns were the fixed setup and launch prompts; no
mathematical intervention occurred. The operator's measurement controls and
`reports/metrics` were not modified and were not used as mathematical input.
Metrics can remain provisional until the operator reconciles usage.
