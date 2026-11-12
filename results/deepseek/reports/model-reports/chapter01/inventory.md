# Coverage inventory — Chapter 1 (source pages 5–11)

Source: `source/Chapter01.pdf`, 7 pages, sha256
`855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17`.
This inventory was derived by reading the complete extracted text and rendering the
chapter pages; no supplied inventory, targets, hints, or prior formalization was used.

Status legend: **D** definition; **P** proved; **R** reused from Mathlib with
attribution; **O** recorded open (statement may be recorded as a `Prop` definition,
but no proof); **N** narrative/explanatory, excluded.

## Section 1.1 — Basic quantities

| ID | Source item | Lean | Status | Notes |
|---|---|---|---|---|
| 1.1.1 | Expectation `E X` (footnote 1: Lebesgue integral) | `HDP.expectation`, `Mathlib` integral | D/R | `expectation μ X = ∫ ω, X ω ∂μ`. |
| 1.1.2 | Variance `Var(X) = E(X - E X)^2` | `ProbabilityTheory.variance`; `HDP.variance_eq_integral` | R/P | Mathlib defines variance as `evariance.toReal`; `variance_eq_integral` identifies it with the integral of the centered square on `MemLp 2`. |
| 1.1.3 | Moment generating function `M_X(t) = E e^{tX}` | `HDP.mgfOf`, `HDP.mgfOf_eq_integral`; Mathlib `ProbabilityTheory.mgf` | D/R | Unfolds to `∫ exp(tX)`. |
| 1.1.4 | p-th moment `E X^p`; absolute moment `E |X|^p` | `HDP.moment`, `HDP.absMoment` | D | Real power (junk for negative base is inherited from `Real.rpow`; statements use `absMoment` where non-negativity matters). |
| 1.1.5 | `L^p` norm for `p ∈ (0,∞)`, and `L^∞ = ess sup |X|` | `HDP.LpNorm` = `MeasureTheory.eLpNorm` | D/R | `eLpNorm` is `(∫ ‖X‖^p)^{1/p}` for finite p and the essential supremum for `p = ∞`. |
| 1.1.6 | `L^p` space `{X : ‖X‖_{L^p} < ∞}` | `HDP.LpSpace` | D | Set of `MemLp X p μ`. |
| 1.1.7 | For `p ∈ [1,∞]`, `‖·‖_{L^p}` is a norm and `L^p` is Banach | `HDP.Lp_complete`, `HDP.L2_innerProductSpace`; Mathlib `Lp` | P/R | `Lp_complete` restates Mathlib's completeness of `MeasureTheory.Lp` for `p ≥ 1`; `L2_innerProductSpace` records the Hilbert-space structure of `L²`. |
| 1.1.8 | For `p < 1`, the triangle inequality fails and `‖·‖_{L^p}` is not a norm | `HDP.triangle_inequality_fails_of_lt_one` (all `0 < p < 1`), plus `triangle_inequality_fails_at_half` | P | Same two-point probability space, now for every real `p ∈ (0,1)`: `‖X+Y‖_{L^p}=1` while `2·(1/2)^{1/p}<1`; the broad source claim is established, not just the `p=1/2` special case. |
| 1.1.9 | `L^2` inner product `⟨X,Y⟩ = E XY` and norm `(E|X|^2)^{1/2}` (1.1) | `HDP.l2Inner`, `HDP.l2Inner_self`, `HDP.LpNorm` | D/P | `l2Inner μ X X = ∫ X^2` proved. |
| 1.1.10 | `‖X - E X‖_{L^2} = sqrt(Var X) = σ(X)` | `HDP.stdDev`, `HDP.stdDev_eq_lpNorm` | P | Proved for `MemLp X 2`. |
| 1.1.11 | Covariance (1.2) `cov(X,Y) = E(X-EX)(Y-EY) = ⟨X-EX,Y-EY⟩` | Mathlib `covariance`; `HDP.covariance_eq_l2Inner` | R/P | The equality is definitional in Mathlib; HDP states it with `l2Inner`. |
| 1.1.12 | Remark 1.1.1, geometric interpretation of covariance | — | N | Interpretive remark; no theorem. |

## Section 1.2 — Classical inequalities and tails

| ID | Source item | Lean | Status | Notes |
|---|---|---|---|---|
| 1.2.1 | Jensen: `φ(E X) ≤ E φ(X)` for convex `φ` | `HDP.jensen` | P | Requires `Integrable X` and `Integrable (φ ∘ X)`; `φ` convex on `univ`. |
| 1.2.2 | (1.3) `‖X‖_{L^p} ≤ ‖X‖_{L^q}` for `0 ≤ p ≤ q ≤ ∞` | `HDP.LpNorm_mono` | P | Probability measure; `AEStronglyMeasurable X`. |
| 1.2.3 | (1.4) Minkowski `‖X+Y‖_{L^p} ≤ ‖X‖_{L^p}+‖Y‖_{L^p}` | `HDP.LpNorm_add_le` | P | `ℝ≥0∞`-valued form, `p ≥ 1`, both in `MemLp p`. |
| 1.2.4 | Cauchy–Schwarz `|E XY| ≤ ‖X‖_{L^2}‖Y‖_{L^2}` | `HDP.cauchy_schwarz` | P | |
| 1.2.5 | Hölder for conjugate `p,q ∈ (1,∞)` | `HDP.holder` | P | `Real.HolderConjugate`; real-valued `lpNorm` form. |
| 1.2.6 | Hölder also holds for `p = 1, q = ∞` | `HDP.holder_one_top` | P | Separate proof using the essential-supremum bound. |
| 1.2.7 | CDF `F_X(t) = P(X ≤ t)` | `HDP.cdfOf`, `HDP.cdfOf_eq_measureReal` | D/P | Identifies CDF with `μ.real {X ≤ t}`. |
| 1.2.8 | Tail `P(X > t) = 1 - F_X(t)` | `HDP.tail`, `HDP.tail_eq_one_sub_cdf` | D/P | Uses `Measure.real` and complement; a.e. measurability hypothesis. |
| 1.2.9 | Lemma 1.2.1 integral identity for non-negative `X` | `HDP.integral_eq_integral_tail` (real), `HDP.lintegral_eq_lintegral_tail` (`ℝ≥0∞`) | P | Real form for `Integrable X`, `0 ≤ᵐ X`; `ℝ≥0∞` form holds generally, which also encodes "finite or infinite simultaneously". |
| 1.2.10 | Exercise 1.2.2 signed integral identity | `HDP.integral_eq_tail_sub_lower` | P | Second integral is over `(-∞,0]`; the endpoint `0` is null, so this is the source's `(-∞,0)` identity. |
| 1.2.11 | Exercise 1.2.3 `E|X|^p = ∫_0^∞ p t^{p-1} P(|X|>t) dt` | `HDP.absMoment_eq_integral_tail_ennreal`, `absMoment_eq_integral_tail_ennreal'`, `absMoment_eq_integral_tail_real` | P | Extended-valued identity and the literal real statement under the source's finiteness hypothesis are both proved; the real form converts the `ℝ≥0∞` layer-cake identity using a.e. finiteness of the tail measures. |
| 1.2.12 | Proposition 1.2.4 Markov `P(X ≥ t) ≤ E X / t` | `HDP.markov`, `HDP.markov_ennreal` | P | Real form for integrable `X`; `markov_ennreal` gives the general `ℝ≥0∞` inequality with only a.e. measurability/non-negativity, so the source's lack of an integrability hypothesis is covered in extended form. |
| 1.2.13 | Corollary 1.2.5 Chebyshev `P(|X-μ| ≥ t) ≤ σ^2/t^2` | `HDP.chebyshev` | P | Uses Mathlib's `meas_ge_le_variance_div_sq`. |
| 1.2.14 | Exercise 1.2.6 deduce Chebyshev from Markov | `HDP.chebyshev_from_markov` | P | Direct Markov-on-`(X-μ)^2` proof, independent of 1.2.13. |
| 1.2.15 | Remark 1.2.7 pointer to Proposition 2.5.2 | — | N | Forward reference; excluded. |

## Section 1.3 — Limit theorems

| ID | Source item | Lean | Status | Notes |
|---|---|---|---|---|
| 1.3.1 | `Var(X_1+...+X_N) = Σ Var(X_i)` for independent variables | `HDP.variance_sum_indep` | P | Pairwise independent finite family, all in `MemLp 2`. |
| 1.3.2 | (1.5) `Var((1/N)Σ X_i) = σ^2/N` for i.i.d. mean `μ`, variance `σ^2` | `HDP.variance_sampleMean` | P | `variance (X 0) = σ^2`; `N > 0`. |
| 1.3.3 | Theorem 1.3.1 strong law of large numbers | `HDP.strong_law` | P/R | Direct wrapper of Mathlib `ProbabilityTheory.strong_law_ae_real` (Etemadi), which needs only integrability, pairwise independence and identical distributions; this is slightly stronger than the source's i.i.d. hypothesis. Conclusion is a.e. convergence of `sampleMean` to `∫ X 0`. |
| 1.3.4 | Theorem 1.3.2 Lindeberg–Lévy central limit theorem | `HDP.central_limit_theorem`, `central_limit_cdf`, `central_limit_tail` | P | Law convergence proved via characteristic-function second-order expansion, the `(1+z/n)^n → e^z` limit, Chebyshev tightness, Prokhorov compactness and uniqueness of the characteristic function. The CDF and tail (`P(Z_N ≥ t) → P(g ≥ t)`) forms stated in the source are derived by Portmanteau with null frontier. |
| 1.3.5 | Density of `N(0,1)` (1.6) | `HDP.gaussianPDFReal_zero_one` | P | Identifies Mathlib's `gaussianPDFReal 0 1` with `1/√(2π) e^{-x^2/2}`. |
| 1.3.6 | Exercise 1.3.3 `E|(1/N)Σ X_i - μ| = O(1/√N)` | `HDP.sampleMean_deviation_isBigO` | P | Big-O with respect to `(√N)^{-1}`, i.i.d. finite variance. Proved via `L^1–L^2`, the variance formula, and Cauchy–Schwarz. |
| 1.3.7 | Bernoulli `Ber(p)`, `E X = p`, `Var X = p(1-p)` | `HDP.bernoulliMeasure`, `HDP.bernoulli_mean`, `HDP.bernoulli_variance` | D/P | Measure on `ℝ` supported on `{0,1}`; requires `p ≤ 1`. |
| 1.3.8 | Binomial `Binom(N,p)` as law of the sum | `HDP.binomialMeasure`, `binomialPMFMeasure` | D/P | `binomialMeasure` is now defined as the law of `∑_{i<N} f_i` under the product of `N` Bernoulli laws, exactly matching the source; Mathlib's `PMF.binomial` is retained as `binomialPMFMeasure` for reference. |
| 1.3.9 | de Moivre–Laplace (1.7) | `HDP.de_moivre_laplace` | P | Proved as the Bernoulli special case of `central_limit_theorem`, with `σ = sqrt(p(1-p))`. |
| 1.3.10 | Poisson `Pois(λ)`, mass function (1.8) | `HDP.poissonDist`, `HDP.poissonDist_apply`, `HDP.poissonPMFReal_eq` | D/R/P | Mathlib's `poissonMeasure` wrapped and its mass function identified. |
| 1.3.11 | Theorem 1.3.4 Poisson limit theorem | `HDP.poisson_limit_theorem`, with `poisson_product_tendsto`, `tight_poisson_sums`, `charFun_poissonReal`, `charFun_bernoulli` | P | Proved for triangular arrays of independent Bernoulli laws: characteristic-function product limit, a.e. non-negativity/integrability of the row sums, uniform mean bound and tightness, then weak convergence to `poissonReal λ`. |

## Section 1.4 — Notes

| ID | Source item | Status | Notes |
|---|---|---|---|
| 1.4.1 | Bibliographic references to [72], [23] for SLLN/CLT | N | Narrative; excluded. |
| 1.4.2 | Attribution of Markov/Chebyshev to Chebyshev | N | Narrative; excluded. |

## Summary

Proved/defined: every mathematical item in Sections 1.1–1.3, including the
`p < 1` failure for every `0 < p < 1`, the CLT with its CDF/tail form,
de Moivre–Laplace, the Poisson limit theorem, the literal real Exercise 1.2.3,
the binomial law as the law of a Bernoulli sum, and the Lp Banach/L² Hilbert
correspondence.  Section 1.4 is narrative and excluded.  The only remaining
caveat is the definition-level convention for `HDP.moment` with a real power and
negative base (Mathlib's `Real.rpow` convention); the absolute moment and all
theorems use `|X|^p` or non-negative contexts.
