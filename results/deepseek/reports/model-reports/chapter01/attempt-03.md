# RESUME_03 report — third continuation

Date: 2026-11-02 (Europe/Athens)
Source: `source/Chapter01.pdf`, 7 pages (book pp. 5–11), sha256
`855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17`.
Pins unchanged: Lean 4.29.0-rc3; Mathlib
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
Agent: same single DeepSeek V4.1 Flash 1017 / High run. No other model, web source,
external repository, Appetizer product, or prior formalization used.

## 1. Outcome

This continuation preserved the first two attempts and re-read the complete source,
the live inventory, `reports/resume-02/final-report.md`, its remaining-obligations
report, and the existing Lean files.

Resolved/strengthened in this continuation:

| Item | Status |
|---|---|
| CLT source form: CDF convergence and tail convergence | **Added** (`central_limit_cdf`, `central_limit_tail`) |
| `p < 1` triangle failure for **all** `0 < p < 1` | **Proved** (`triangle_inequality_fails_of_lt_one`) |
| Markov without an integrability hypothesis | **Added** (`markov_ennreal`) |
| Poisson limit theorem (Theorem 1.3.4) | **Still open** |

The chapter is **not complete**.  The Poisson limit theorem remains unproved, and
the self-review also records two correspondence gaps that are not the Poisson
theorem: the literal real-arithmetic form of Exercise 1.2.3 and the identification
of `binomialMeasure` with the law of a Bernoulli sum.

## 2. Source self-review (same-agent, not independent)

I re-read the original PDF text rather than only the status labels.  Concrete
findings and actions:

1. **`p < 1` row was too narrow.**  The prior proof covered only `p = 1/2`, which
   does not establish the source's broad “for `p < 1`” claim.  I generalized the
   same two-point counterexample to every real `p ∈ (0,1)`:
   `‖X+Y‖_{L^p}=1` and `‖X‖_{L^p}=‖Y‖_{L^p}=(1/2)^{1/p}`, so the triangle
   inequality would require `1 ≤ 2·(1/2)^{1/p} = 2^{1-1/p} < 1`.
   This is now `HDP.triangle_inequality_fails_of_lt_one`.
2. **CLT source form.**  The prior theorem gave weak/law convergence.  The source
   explicitly defines convergence in distribution as pointwise CDF convergence and
   states the tail form `P(Z_N ≥ t) → P(g ≥ t)`.  I added
   `HDP.central_limit_cdf` and `HDP.central_limit_tail`, proved from the law
   convergence by the Portmanteau theorem with null frontier `{t}`.
3. **Markov integrability.**  The prior real Markov theorem assumed `Integrable X`;
   the source does not assume finite expectation.  I added the `ℝ≥0∞` form
   `HDP.markov_ennreal` with only a.e. measurability and a.e. non-negativity.
4. **Exercise 1.2.3 remains a correspondence gap.**  The formal theorem is the
   stronger `ℝ≥0∞` layer-cake identity; the literal real statement with the
   source's “whenever the right-hand side is finite” hypothesis is not separately
   derived.  This is now labelled partial, not quietly counted as the literal target.
5. **Binomial identification gap.**  `binomialMeasure` is Mathlib's
   `PMF.binomial`; the theorem that this is the law of a sum of i.i.d. Bernoulli
   variables was not proved.  Labelled partial correspondence.
6. **Lp Banach claim.**  No local HDP declaration restates Mathlib's completeness
   of `Lp` for `p ≥ 1`; the inventory records it as a reused Mathlib instance rather
   than a local theorem.
7. The SLLN wrapper uses pairwise independence, a weaker hypothesis than i.i.d.;
   this generalizes rather than narrows the source.  No defect.
8. The first-attempt and resume-02 reports are preserved unchanged except for a
   continuation note in `reports/final-report.md`.

## 3. Poisson limit: actual work and exact remaining obstruction

Completed foundations remain in `lean/HDP/PoissonCharFun.lean`:

- `poissonReal r` — Poisson law on `ℝ`;
- `charFun_poissonReal` — `charFun (poissonReal r) t = exp(r(e^{it}−1))`;
- `charFun_bernoulli` — `charFun (bernoulliMeasure p) t = 1 − p + p e^{it}`.

Work attempted in this continuation toward the product limit:

- Re-proved the unweighted finite-product perturbation bound
  `‖∏a − ∏b‖ ≤ M^card ∑‖a−b‖` (for `M ≥ 1`) in a scratch file.  This bound is
  not sufficient here because `M^N` can grow faster than the small factor
  `max p_{N,i}`.
- Developed the correct per-factor weighted perturbation bound
  `‖∏a − ∏b‖ ≤ ∑_i ‖a_i−b_i‖ ∏_{j≠i} max(‖a_j‖,‖b_j‖)`.
  The induction proof was brought to its final `Finset.sum_insert`/`erase_insert`
  algebra but not completed; the unfinished scratch file is not part of
  `lean/HDP/` and nothing was added as an axiom or theorem.
- The plan after that bound: bound `max(‖1+u_i‖,‖exp u_i‖) ≤ exp(p_i|z−1|)`,
  use `‖(1+u_i)−exp(u_i)‖ ≤ (3/4)‖u_i‖²` from `Complex.exp_bound`, and
  `∑p_i² ≤ (max p_i)∑p_i → 0`, giving the product limit.
- Tightness of the Bernoulli sums is not yet formalized; planned via Markov on
  `S_N ≥ M` and `E S_N = ∑ p_{N,i} → λ`.

The obstruction is the unfinished finite-product/log-limit formalization, not a
missing statement or a mathematical impossibility.  No claim of completion is made.

## 4. Verification

`tools/lake.sh build`:

```
Build completed successfully (8061 jobs).
```

No `sorry`, `admit`, custom axiom, or `unsafe` proof.  Axiom inspection
(`reports/resume-03/axiom-check.txt`) of the new declarations
`central_limit_cdf`, `central_limit_tail`,
`triangle_inequality_fails_of_lt_one`, `markov_ennreal`, plus the CLT and
de Moivre theorems, shows only:

```
propext, Classical.choice, Quot.sound
```

## 5. Remaining obligations

1. **Theorem 1.3.4, Poisson limit theorem** — product limit, tightness, final
   weak-convergence assembly.  Exact statement remains
   `HDP.PoissonLimitTheorem`.
2. **Exercise 1.2.3 literal real form** — derive the real identity from the
   extended-valued layer-cake theorem under the source's finiteness hypothesis.
3. **Binomial law identification** — prove `binomialMeasure N p` is the law of
   the sum of `N` i.i.d. Bernoulli variables.
4. **Lp Banach/Hilbert correspondence** — optionally restate Mathlib's `Lp`
   completeness and `L²` inner-product instances locally, or keep as explicit
   Mathlib reuse (current inventory wording).

## 6. Files

- `lean/HDP/CLT.lean` — added `central_limit_cdf`, `central_limit_tail`.
- `lean/HDP/Sharpness.lean` — added general `0 < p < 1` counterexample and its
  `L^p` norm computations.
- `lean/HDP/Tails.lean` — added `markov_ennreal`.
- `reports/coverage-inventory.md` — updated honestly.
- `reports/resume-03/` — this report, axiom evidence, remaining work.

## 7. Metric snapshot (observational only)

`reports/metrics/latest-measurement-summary.json` at read time reported
`generated_at = 2026-11-02T14:47:32Z`, `state = running`,
`request_count = 55`, `wall_elapsed_seconds = 1054.932`,
`api_busy_wall_seconds = 431.817`, `known_cost_usd = 0.246130114`; input/output
token fields were absent and remain unknown.  `latest-summary.json` reported
`request_count = 56`, `known_cost_usd = 0.249478248`.  These are provisional
observational metadata, not mathematical input.

## 8. Honest final status

CLT (including CDF/tail form), de Moivre–Laplace, and the `p < 1` claim for all
`0 < p < 1` are proved.  The Poisson limit theorem remains open.  The chapter is
not source-complete.  This is self-review plus kernel checking, not independent
semantic review.
