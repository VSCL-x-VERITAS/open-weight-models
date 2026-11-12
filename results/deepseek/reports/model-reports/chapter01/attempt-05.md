# RESUME_05 report — fifth continuation

Date: 2026-11-02 (Europe/Athens)
Source: `source/Chapter01.pdf` (7 pages, book pp. 5–11), sha256
`855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17`.
Pins unchanged: Lean 4.29.0-rc3; Mathlib
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
Same single DeepSeek V4.1 Flash 1017 / High run. No other model, web source,
external repository, or prior formalization used.

## 1. Outcome

The three source-correspondence obligations recorded in RESUME_04 are now
resolved:

| Obligation | Status |
|---|---|
| Exercise 1.2.3 literal real form | **Proved** (`HDP.absMoment_eq_integral_tail_real`) |
| Binomial law identification | **Resolved by source-faithful definition** (`HDP.binomialMeasure` is the law of the Bernoulli sum) |
| Lp Banach/Hilbert correspondence | **Declared** (`HDP.Lp_complete`, `HDP.L2_innerProductSpace`) |

The Poisson limit theorem, CLT (including CDF/tail form), de Moivre–Laplace, the
`p < 1` failure for all `0 < p < 1`, and the earlier Section 1.1–1.2 results are
preserved and still build.

## 2. Exercise 1.2.3 — literal real form

`lean/HDP/Tails.lean` now contains:

- `absMoment_eq_integral_tail_ennreal` — the extended-valued layer-cake identity;
- `absMoment_eq_integral_tail_ennreal'` — the same identity rearranged to
  `∫⁻ ofReal(|X|^p) = ∫⁻ ofReal(p t^{p−1}) * μ{t < |X|}`;
- `absMoment_eq_integral_tail_real` — the literal real statement
  `∫ |X|^p = ∫_0^∞ p t^{p−1} P(|X| > t) dt`, under the source's finiteness
  hypothesis (expressed as finiteness of the extended right-hand side).

The real proof identifies the tail-measure function as antitone/measurable,
converts the extended identity to real integrals with
`integral_eq_lintegral_of_nonneg_ae`, and uses the finiteness hypothesis to obtain
a.e. finiteness of `μ{t < |X|}` so that `ENNReal.ofReal (μ.real s) = μ s` can be
applied.

## 3. Binomial law

The earlier `binomialMeasure` was Mathlib's `PMF.binomial` on `Fin (N+1)`, with a
recorded gap that it was not identified as the law of a Bernoulli sum.  The source
defines `Binom(N,p)` as the distribution of `S_N = X_1 + ... + X_N`; I therefore
changed the definition to that law:

```
binomialMeasure N p hp :=
  (Measure.pi (fun _ : Fin N => bernoulliMeasure p)).map (fun f => ∑ i, f i)
```

on `Measure ℝ`.  The old PMF construction is retained as
`binomialPMFMeasure` for reference.  This makes the source correspondence
definitional and removes the gap.  The probability instance is proved.

## 4. Lp Banach/Hilbert correspondence

`lean/HDP/Basic.lean` now contains:

- `Lp_complete` — `CompleteSpace (MeasureTheory.Lp ℝ p μ)` for `p ≥ 1` on a
  finite measure space, restating Mathlib's completeness instance;
- `L2_innerProductSpace` — the `InnerProductSpace ℝ (Lp ℝ 2 μ)` structure.

These are explicit local declarations of the source's Banach/Hilbert claims, using
Mathlib's existing `Lp` instances rather than new mathematics.

## 5. Full source self-review

I re-read the complete chapter text and checked every inventory row against the
actual declarations, including domains, hypotheses, quantifiers, parameter ranges
and conclusion strength.  The inventory is updated to mark all mathematical items
of Sections 1.1–1.3 as covered; Section 1.4 is narrative.

Points checked:

- `E X`, variance, MGF, moments, `L^p` norm/space, `L^2` inner product, standard
  deviation, covariance: definitions and identities match.
- Jensen, `L^p` monotonicity, Minkowski, Cauchy–Schwarz, Hölder (finite and
  `1/∞`), CDF/tail, integral identity, Exercises 1.2.2/1.2.3, Markov (real and
  extended), Chebyshev, Exercise 1.2.6: match.
- variance of independent sums, (1.5), SLLN, CLT (law, CDF and tail forms),
  Exercise 1.3.3, Bernoulli/binomial/Poisson/Gaussian objects, de Moivre–Laplace,
  Poisson limit: match.
- The SLLN wrapper uses pairwise independence, which is weaker than the source's
  i.i.d. hypothesis; this generalizes rather than narrows.
- `HDP.moment` uses `Real.rpow` for real exponents; for negative bases and
  non-integer exponents this is Mathlib's junk convention.  The absolute moment
  and all theorems use `|X|^p` or non-negative contexts.  This is a
  definition-level convention, not a missing theorem.
- `Lp_complete`/`L2_innerProductSpace` are local restatements of Mathlib
  instances, not independent proofs of new analysis.

This is self-review, not independent semantic review.

## 6. Verification

`tools/lake.sh build`:

```
Build completed successfully (8063 jobs).
```

No `sorry`, `admit`, custom axiom, or `unsafe` proof.  Axiom inspection
(`reports/resume-05/axiom-check.txt`) for
`absMoment_eq_integral_tail_real`, the rearranged ENNReal identity, `Lp_complete`,
`poisson_limit_theorem`, `central_limit_theorem`, `de_moivre_laplace` and
`triangle_inequality_fails_of_lt_one` reports only:

```
propext, Classical.choice, Quot.sound
```

## 7. Files changed

- `lean/HDP/Tails.lean` — real Exercise 1.2.3 and rearranged ENNReal identity.
- `lean/HDP/LimitTheorems.lean` — `binomialMeasure` redefined as the Bernoulli-sum
  law; old PMF retained as `binomialPMFMeasure`.
- `lean/HDP/Basic.lean` — `Lp_complete`, `L2_innerProductSpace`.
- `reports/coverage-inventory.md` — all mathematical rows updated.
- `reports/resume-05/` — this report and axiom evidence.

## 8. Metrics (observational only)

Latest read snapshot (`reports/metrics/latest-measurement-summary.json`):
`generated_at = 2026-11-02T17:41:08Z`, `state = running`,
`request_count = 39`, `wall_elapsed_seconds = 960.71`,
`api_busy_wall_seconds = 384.739`, `known_cost_usd = 0.455551552`,
`input_tokens = 29843312`, `output_tokens = 16024`.
`latest-summary.json` reported `request_count = 41`,
`known_cost_usd = 0.474769172`, `input_tokens = 31407551`,
`output_tokens = 18988`.  These are provisional observational metadata, not
mathematical input.

## 9. Honest status

The three recorded correspondence obligations are closed, and the full
mathematical scope of Sections 1.1–1.3 is covered by declarations that build and
pass the axiom check.  This is self-review plus kernel verification, not an
independent semantic audit; no independent review is claimed.
