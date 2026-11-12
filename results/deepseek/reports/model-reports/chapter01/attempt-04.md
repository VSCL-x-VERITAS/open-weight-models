# RESUME_04 report — fourth continuation

Date: 2026-11-02 (Europe/Athens)
Source: `source/Chapter01.pdf` (7 pages, book pp. 5–11), sha256
`855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17`.
Pins unchanged: Lean 4.29.0-rc3; Mathlib
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
Same single DeepSeek V4.1 Flash 1017 / High run. No other model, web source,
external repository, or prior formalization was used.

## 1. Main result of this continuation

**Theorem 1.3.4 (Poisson limit theorem) is now proved** as
`HDP.poisson_limit_theorem` in `lean/HDP/PoissonLimit.lean`.

This was the last major open theorem of the chapter.  The proof is complete at the
source's full triangular-array strength:

- `X N i` are random variables with `μ.map (X N i) = bernoulliMeasure (p N i)`;
- each row `(X N i)_{i<N}` is independent (`iIndepFun`);
- `max_{i<N} p_{N,i} → 0` and `∑_{i<N} p_{N,i} → λ`.

The conclusion is convergence in distribution of
`S_N = ∑_{i<N} X_{N,i}` to the Poisson law `Pois(λ)`, represented as the
pushforward `poissonReal λ` of Mathlib's `poissonMeasure λ` on `ℕ` to `ℝ`.

### New Poisson proof components

- `lean/HDP/PoissonLimit.lean`:
  - `charFun_sum_bernoulli_row` — the characteristic function of a row sum is the
    product of the Bernoulli characteristic functions;
  - `ae_nonneg_of_map_bernoulli`, `memLp_of_map_bernoulli`,
    `integral_of_map_bernoulli`, `ae_nonneg_sum_row`, `integral_sum_row`,
    `integrable_sum_row`;
  - `exists_sum_bound` — the row sums `∑ p_{N,i}` have a uniform bound after
    discarding finitely many initial rows;
  - `tight_poisson_sums` — tightness of the laws of the row sums, via Markov and
    the uniform mean bound;
  - `poisson_limit_theorem` — final weak-convergence assembly using
    `tendsto_probabilityMeasure_of_charFun` and `charFun_poissonReal`.
- `lean/HDP/PoissonProduct.lean`:
  - `norm_prod_sub_prod_range_le` — the finite-product perturbation bound
    `‖∏ a_i − ∏ b_i‖ ≤ (∏ M_i) ∑ ‖a_i−b_i‖` for `M_i ≥ 1`;
  - `sum_sq_tendsto_zero` — `∑ p_{N,i}² → 0` from `max p → 0` and
    `∑ p → λ`;
  - `prod_diff_tendsto_zero` — the product difference tends to zero with
    `M_i = exp(c p_{N,i})`;
  - `prod_exp_tendsto` and `poisson_product_tendsto` — the product limit
    `∏ (1 − p_i + p_i e^{it}) → exp(λ(e^{it}−1))`.

The earlier product-perturbation attempts are superseded by the range-based bound
above; the weighted `Finset.erase` route was abandoned only after the range proof
succeeded.

## 2. Verification

`tools/lake.sh build`:

```
Build completed successfully (8063 jobs).
```

No `sorry`, `admit`, custom axiom, or `unsafe` proof.  Axiom inspection
(`reports/resume-04/axiom-check.txt`) of `poisson_limit_theorem`,
`tight_poisson_sums`, `poisson_product_tendsto`, `charFun_poissonReal` and
`central_limit_theorem` reports only:

```
propext, Classical.choice, Quot.sound
```

## 3. Self-review and still-open correspondence gaps

The live inventory now marks Theorem 1.3.4 as proved.  I re-checked the final
Poisson statement against the source: the row variables are Bernoulli, independent,
the maxima tend to zero, the means tend to a finite `λ`, and the conclusion is
distributional convergence to `Pois(λ)`.  The pushforward to `ℝ` is the standard
measure-theoretic representation of a distribution on `{0,1,2,...}`.

Still open (not hidden):

1. **Exercise 1.2.3, literal real form.**  The formal theorem
   `HDP.absMoment_eq_integral_tail_ennreal` is the stronger `ℝ≥0∞` layer-cake
   identity.  I attempted the conversion to
   `∫ |X|^p = ∫_0^∞ p t^{p−1} P(|X|>t) dt` under the source's “RHS finite”
   hypothesis: the ENNReal identity was put in the exact shape
   `∫⁻ ofReal(|X|^p) = ∫⁻ ofReal(p t^{p−1}) * μ{t< |X|}` (lemma
   `absMoment_eq_integral_tail_ennreal'` in a scratch attempt), but the final
   conversion to the real interval integral and the a.e.-finiteness bookkeeping
   were not completed.  It is not counted as a proof of the literal real target.
2. **Binomial law identification.**  `binomialMeasure` is Mathlib's
   `PMF.binomial`; the statement that it is the law of a sum of `N` i.i.d.
   Bernoulli variables is still not proved.
3. **Lp Banach/Hilbert correspondence.**  The inventory records Mathlib's `Lp`
   completeness/inner-product instances as reuse; no local HDP declaration
   restates them.

## 4. Files

- `lean/HDP/PoissonLimit.lean` (new): Poisson theorem and prerequisites.
- `lean/HDP/PoissonProduct.lean` (new/expanded): product limit and perturbation
  bounds.
- `lean/HDP/OpenStatements.lean`: comment updated; Poisson statement record is
  now superseded by the theorem.
- `reports/coverage-inventory.md`: Theorem 1.3.4 marked proved; remaining gaps
  retained.
- `reports/resume-04/`: this report and axiom evidence.

## 5. Metrics (observational only)

At read time `reports/metrics/latest-measurement-summary.json` reported
`generated_at = 2026-11-02T15:55:33Z`, `state = running`,
`request_count = 110`, `wall_elapsed_seconds = 3178.251`,
`api_busy_wall_seconds = 875.995`, `known_cost_usd = 0.561915899`;
input/output token fields were absent and remain unknown.  `latest-summary.json`
reported `request_count = 111`, `known_cost_usd = 0.565761811`.  These are
provisional observational metadata, not mathematical input.

## 6. Honest status

The Poisson limit theorem — the primary remaining obligation — is proved.
The chapter is **not fully source-complete** because the three correspondence gaps
in §3 remain.  No independent semantic review is claimed; this is self-review plus
kernel checking.  No unfinished scratch draft is in `lean/HDP/`.
