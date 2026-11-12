# Final report — Chapter 1 formalization (partial, with named open items)

Date: 2026-11-02 (Europe/Athens)
Source: `source/Chapter01.pdf` (7 pages; book pages 5–11; sha256
`855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17`)
Pins: Lean 4.29.0-rc3; Mathlib `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`
Agent: single DeepSeek agent (`deepseek/deepseek-v4.1-flash-1017`); no other model,
web resource, prior formalization, or user-global material was used.

## 1. Result

The chapter has been read completely and inventoried.  All Section 1.1–1.2
mathematical items except the explanatory negative claim 1.1.8 are formalized, and
all Section 1.3 items except the three limit theorems are formalized.  The library
builds with no `sorry`, `admit`, custom axiom, or `unsafe` proof.

**The development is not complete.** Three central limit theorems are open:

1. **Theorem 1.3.2, Lindeberg–Lévy CLT** — no proof.
2. **(1.7), de Moivre–Laplace theorem** — no proof (it is the Bernoulli special case
   of the open CLT).
3. **Theorem 1.3.4, Poisson limit theorem** — no proof.

Their exact intended formal statements are recorded as `Prop`-valued definitions in
`lean/HDP/OpenStatements.lean` (`HDP.CentralLimitTheorem`, `HDP.CLTConclusion`,
`HDP.DeMoivreLaplaceTheorem`, `HDP.PoissonLimitTheorem`).  They are **not** theorems
and nothing in the completed part depends on them.

Actual cause: the pinned Mathlib has no CLT, no Lévy continuity theorem for
characteristic functions, and no Poisson approximation theorem.  Proving the CLT
would require formalizing (at least) the characteristic-function Taylor expansion
for i.i.d. variables and Lévy's continuity theorem, including tightness/Prokhorov
arguments; the Poisson theorem would require a Poisson approximation/coupling
argument.  This was not completed in the available run.  No easier substitute
statement was introduced.

The remaining open item 1.1.8 (`p < 1` triangle inequality fails) is an explanatory
negative claim; no counterexample was formalized.

## 2. Files

| File | Contents |
|---|---|
| `lean/HDP/Basic.lean` | Definitions: expectation, sample mean, `L^p` norm/space, `L^2` inner product, standard deviation, moments, MGF, CDF, tail, convergence in distribution; `stdDev_eq_lpNorm`, `covariance_eq_l2Inner`, `l2Inner_self`. |
| `lean/HDP/Inequalities.lean` | Jensen, `L^p` monotonicity, Minkowski, Hölder (finite and `1/∞`), Cauchy–Schwarz. |
| `lean/HDP/Tails.lean` | Lemma 1.2.1, Exercises 1.2.2/1.2.3, Markov, Chebyshev, Exercise 1.2.6, CDF/tail relation. |
| `lean/HDP/LimitTheorems.lean` | Variance of sums, formula (1.5), SLLN, Exercise 1.3.3, Bernoulli/binomial/Poisson/Gaussian objects. |
| `lean/HDP/OpenStatements.lean` | Precise open propositions for CLT, de Moivre–Laplace and Poisson limit; no proofs. |
| `lean/HDP.lean` | Imports the five modules above. |

Coverage table: `reports/coverage-inventory.md`.

## 3. Compiler and kernel verification

`tools/lake.sh build` completed successfully:

```
Build completed successfully (8055 jobs).
```

(`lean/HDP.lean` imports all five modules; `HDP.OpenStatements` contains definitions
only.)

Axiom inspection (`reports/axiom-check.txt`) for 24 key declarations
(`jensen`, `holder`, `holder_one_top`, `integral_eq_integral_tail`,
`integral_eq_tail_sub_lower`, `markov`, `chebyshev`, `chebyshev_from_markov`,
`variance_sampleMean`, `strong_law`, `sampleMean_deviation_isBigO`,
`stdDev_eq_lpNorm`, `poissonDist_apply`, `gaussianPDFReal_zero_one`, etc.) shows
only the standard axioms:

```
propext, Classical.choice, Quot.sound
```

No declaration depends on `sorryAx`, a custom axiom, or an `unsafe` proof.  Source
search for forbidden proof placeholders in `lean/HDP/` found none.

## 4. Source/statement self-review (not an independent audit)

This section is **self-review by the same agent**, not an independent semantic
audit and not a second reviewer.

Checked against the source:

- Domains: probability measure `[IsProbabilityMeasure μ]` is present throughout;
  real-valued random variables; integrability/L² hypotheses added exactly where
  the real-valued identity needs them (Jensen, integral identity, Markov,
  Chebyshev, variance formula).
- Quantifiers: `∀ t > 0`, `∀ p ∈ (0,∞)`, `0 ≤ p ≤ q`, conjugate exponents, and
  `N > 0` are preserved.  The SLLN is a.e. convergence of `(X_0+...+X_{N-1})/N`.
- Constants: `p(1-p)` for Bernoulli, `σ²/N` in (1.5), `1/√(2π)` in the normal
  density, and the Poisson mass `e^{-λ}λ^k/k!` are preserved.
- Conclusion strength: no hypothesis-only or weakened variants replaced the named
  results.  The open CLT/Poisson targets were not disguised as proved.

Deliberate, documented differences:

1. **SLLN assumptions are weaker than the source's i.i.d.**: the Mathlib theorem
   used (`strong_law_ae_real`, Etemadi) requires only integrability, pairwise
   independence and identical distributions.  The conclusion is the same and the
   theorem therefore implies the source statement; the hypothesis is generalized,
   not narrowed.
2. **Exercise 1.2.3 is stated in `ℝ≥0∞`**: the source gives the real identity
   "whenever the right-hand side is finite".  The formal identity is the stronger
   extended-valued layer-cake identity.  The real-arithmetic restatement with the
   exact finiteness side condition was not separately derived.
3. **Exercise 1.2.2 uses `(-∞,0]`** rather than the source's `(-∞,0)`; the
   endpoint `0` is Lebesgue-null and the identity is unchanged.
4. **CDF/tail** use `μ.real` and require a.e. measurability of `X`.
5. **Minkowski/monotonicity** are stated with Mathlib's `ℝ≥0∞`-valued `eLpNorm`;
   Hölder/Cauchy–Schwarz are stated with the real-valued `lpNorm` and `toReal`
   correspondence is made explicitly in proofs.
6. **Bernoulli** is a measure on `ℝ` supported on `{0,1}`; **binomial** uses
   Mathlib's `PMF.binomial` on `Fin (N+1)`; **Poisson** wraps Mathlib's
   `poissonMeasure` on `ℕ`.

## 5. Reused Mathlib results (explicit attribution)

- `ProbabilityTheory.strong_law_ae_real` — `Mathlib/Probability/StrongLaw.lean`
  (Sébastien Gouëzel; Etemadi's proof).
- `MeasureTheory.Integrable.integral_eq_integral_meas_lt`,
  `lintegral_eq_lintegral_meas_lt`, `lintegral_rpow_eq_lintegral_meas_lt_mul` —
  `Mathlib/MeasureTheory/Integral/Layercake.lean`,
  `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean`.
- `ConvexOn.map_integral_le` — `Mathlib/Analysis/Convex/Integral.lean`.
- `eLpNorm_le_eLpNorm_of_exponent_le`, `eLpNorm_add_le`,
  `integral_mul_norm_le_Lp_mul_Lq`, `lpNorm_one_eq_integral_norm` — Mathlib `Lp`
  seminorm files and `MeasureTheory/Integral/MeanInequalities.lean`.
- `mul_meas_ge_le_integral_of_nonneg` (Markov) —
  `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.
- `meas_ge_le_variance_div_sq` (Chebyshev),
  `IndepFun.variance_sum`, `variance_eq_integral`, `variance_sub_const` —
  `Mathlib/Probability/Moments/Variance.lean`.
- `IdentDistrib.variance_eq`, `IdentDistrib.integral_eq`,
  `IdentDistrib.measure_mem_eq` — `Mathlib/Probability/IdentDistrib.lean`.
- `cdf_eq_real`, `Measure.map_measureReal_apply`, `measureReal_compl₀` — Mathlib
  CDF/measure files.
- `PMF.binomial` — `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean`.
- `poissonMeasure`, `poissonPMFReal`, `poissonPMF` —
  `Mathlib/Probability/Distributions/Poisson.lean` (Josha Dekker).
- `gaussianReal`, `gaussianPDFReal` —
  `Mathlib/Probability/Distributions/Gaussian/Real.lean`.

## 6. Source issues noticed

- Footnote 3 writes "for all `t ∈ [0,1]`" while using a parameter `λ`; this is a
  source typo in the convexity definition (the standard condition is
  `λ ∈ [0,1]`).
- The SLLN statement writes `S_N = X_1 + ··· X_N` (missing `+`); interpreted as
  `X_1 + ··· + X_N`.
- The source's `p`-moment identity is stated in real arithmetic with a finiteness
  side condition; the formal development uses the `ℝ≥0∞` layer-cake version (see
  §4).
- The proofs of SLLN and CLT are not in the chapter; the Notes refer to external
  textbooks.  The development reused Mathlib's SLLN proof and left the CLT/Poisson
  limits open because no corresponding formal proof is available in the pinned
  library.

## 7. Metric snapshot (observational metadata only)

At the time of writing, `reports/metrics/latest-summary.json` reported (run
`2026-11-02T07-42-32-723Z-8289d7fc-d2a6-4086-bf93-5c6a870b4e67`, state
`running`): `wall_elapsed_seconds = 1885.943`, `api_busy_wall_seconds = 665.551`,
`request_count = 172`, `input_tokens = 23845502`, `output_tokens = 118078`,
`known_cost_usd = 0.314851778`.  `reports/metrics/latest-measurement-summary.json`
(08:15Z) reported `request_count = 175`, `known_cost_usd = 0.319346808`.  These
values are provisional and operator-reconciled; they are not mathematical input.

## 8. Interventions and process notes

- No user intervention beyond the two fixed launch prompts and the initial setup
  request.  No other model, web search, external repository, or prior project
  material was used.
- No pins, toolchain, model endpoint, access policy, or measurement control was
  changed; no `lake update` was run.
- Setup readiness is recorded in `reports/setup-readiness.md`.
- Scratch files in `.scratch/` are temporary compiler probes; they are not part of
  the library and should not be treated as source coverage.

## 9. Honest completion statement

Completed: Section 1.1 definitions and the L² geometry; Section 1.2 inequalities,
integral identity, both exercises 1.2.2/1.2.3 (extended-valued form), Markov,
Chebyshev, Exercise 1.2.6, CDF/tail; Section 1.3 variance identities, SLLN,
Exercise 1.3.3, Bernoulli/binomial/Poisson/Gaussian definitions and mass/density
formulas.

Open: CLT (1.3.2), de Moivre–Laplace (1.7), Poisson limit (1.3.4), and the negative
`p < 1` claim (1.1.8).  The three limit theorems are recorded as precise open
propositions in `lean/HDP/OpenStatements.lean`; none is proved.  Consequently this
is a partial formalization, and no claim of source-complete kernel verification is
made.
