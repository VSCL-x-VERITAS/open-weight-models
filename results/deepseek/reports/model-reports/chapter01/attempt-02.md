# RESUME_02 report — Chapter 1 continuation

Date: 2026-11-02 (Europe/Athens)
Source: `source/Chapter01.pdf`, 7 pages (book pp. 5–11), sha256
`855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17`
Pins unchanged: Lean 4.29.0-rc3; Mathlib
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
Agent: same single DeepSeek V4.1 Flash 1017 / High run; no other model, web
resource, external repository, or prior formalization used.

## 1. Outcome

This continuation started from the saved first attempt.  It **resolved three of the
four obligations** identified by the operator and left one open:

| Obligation | Status |
|---|---|
| Theorem 1.3.2, Lindeberg–Lévy CLT | **Proved** (`HDP.central_limit_theorem`) |
| Formula (1.7), de Moivre–Laplace | **Proved** (`HDP.de_moivre_laplace`) |
| `p < 1` triangle-inequality failure | **Proved** (`HDP.triangle_inequality_fails_at_half`) |
| Theorem 1.3.4, Poisson limit theorem | **Open** |

The build succeeds with no `sorry`, `admit`, custom axiom, or `unsafe` proof.
The Poisson limit is not hidden or weakened; its exact statement remains in
`HDP.PoissonLimitTheorem`, and the preliminary characteristic-function facts that
were completed are in `HDP.PoissonCharFun`.

The first-attempt report is preserved at `reports/final-report.md`; the live
inventory is `reports/coverage-inventory.md`.

## 2. New mathematics and proof architecture

### 2.1 CLT

New files:

- `lean/HDP/WeakConvergence.lean` — generic weak-convergence result on `ℝ`:
  pointwise convergence of characteristic functions plus tightness implies weak
  convergence.  The proof uses Prokhorov compactness of the closure of a tight set,
  the subsequence characterization of compactness, the bounded-continuous integral
  characterization of weak convergence, and `Measure.ext_of_charFun` for uniqueness.
- `lean/HDP/CharFunTaylor.lean` — second-order Taylor expansion of the
  characteristic function at zero:
  `(charFun ν s - 1) / s^2 → -(∫ x² ∂ν)/2` for a law `ν` with mean zero and finite
  second moment.  The pointwise Taylor estimates use `Complex.exp_bound` and a
  dominated-convergence argument with bound `3*x^2` (the bound splits on
  `|s*x| ≤ 1` versus `|s*x| > 1`).
- `lean/HDP/CLT.lean` — the full CLT:
  - characteristic function of a finite independent sum factors as a product;
  - for i.i.d. normalized sums, `N * (φ(t/(σ√N)) - 1) → -t²/2`;
  - `(1 + z_N)^N → exp(-t²/2)` via
    `Complex.tendsto_one_add_pow_exp_of_tendsto`;
  - Chebyshev gives `variance Z_N = 1` and tightness;
  - the generic weak-convergence lemma gives convergence to `gaussianReal 0 1`.

The formal conclusion is law convergence:
`Tendsto (fun N => law of Z_N) atTop (𝓝 ⟨gaussianReal 0 1⟩)`, which is the
measure-theoretic form of “converges in distribution to `N(0,1)`”.  The normalized
variable is
`Z_N = (∑_{i<N} (X_i - m)) / (σ √N)`.

### 2.2 de Moivre–Laplace

`lean/HDP/DeMoivreLaplace.lean` derives the Bernoulli special case from the CLT.
It proves `MemLp id 2 (bernoulliMeasure p)`, transfers the law and second moment to
the `X_i`, and applies the CLT with `m = p`, `σ = sqrt(p(1-p))`.  The source's
assumption that the `X_i` are random variables is represented by the explicit
measurability hypothesis `hXmeas`.

### 2.3 `p < 1` failure

`lean/HDP/Sharpness.lean` gives a concrete two-point probability space and
indicators `X = 1_{true}`, `Y = 1_{false}`.  It proves
`‖X+Y‖_{L^{1/2}} = 1` while `‖X‖_{L^{1/2}} + ‖Y‖_{L^{1/2}} = 1/2`, so the triangle
inequality fails for `p = 1/2 < 1`.

## 3. Poisson limit: exact partial status and attempts

Proved in `lean/HDP/PoissonCharFun.lean`:

- `poissonReal r` — the Poisson law on `ℝ` (the pushforward of Mathlib's
  `poissonMeasure` on `ℕ` under `n ↦ (n : ℝ)`);
- `charFun_poissonReal`:
  `charFun (poissonReal r) t = exp (r (e^{it} - 1))`;
- `charFun_bernoulli`:
  `charFun (bernoulliMeasure p) t = 1 - p + p e^{it}`.

Still open for Theorem 1.3.4:

1. the product limit
   `∏_{i<N} (1 + p_{N,i}(e^{it}-1)) → exp(λ(e^{it}-1))`
   from `max p_{N,i} → 0` and `∑ p_{N,i} → λ`;
2. tightness of the laws of `S_N = ∑_{i<N} X_{N,i}`;
3. assembly via the same weak-convergence lemma.

Concrete attempts made:

- developed a complex `log (1+z)` route using
  `Complex.norm_log_one_add_sub_self_le` and intended `∑ log` of the product;
- developed a product-perturbation route toward
  `∏(1+u_i) - ∏ exp(u_i) → 0` using the second-order exponential Taylor bound and
  a finite-product perturbation estimate.  The perturbation estimate was drafted
  in a scratch file but its final induction algebra and the subsequent product-limit
  formalization were not completed.  Nothing from that unfinished draft is included
  as a theorem in `lean/HDP/`.
- tightness was not formalized; it would follow from
  `P(S_N ≥ M) ≤ E S_N / M` and the boundedness of `E S_N` near `λ`.

This is recorded as open work, not as an external impossibility.  The remaining
gap is a concrete formalization task (product/log limit plus tightness), not a
missing statement or an axiom.

## 4. Compiler and axiom evidence

`tools/lake.sh build`:

```
Build completed successfully (8061 jobs).
```

Axiom inspection (`reports/resume-02/axiom-check.txt`) for the new declarations
`central_limit_theorem`, `de_moivre_laplace`,
`triangle_inequality_fails_at_half`, `charFun_centered_taylor`,
`tendsto_probabilityMeasure_of_charFun`, `charFun_poissonReal`,
`charFun_bernoulli`, `tight_Z`, and the earlier `strong_law` shows only:

```
propext, Classical.choice, Quot.sound
```

No declaration depends on `sorryAx`, a custom axiom, or an `unsafe` proof.

## 5. Self-review of the new statements (same-agent review)

- CLT: hypotheses are i.i.d. (`iIndepFun` + `IdentDistrib`), `MemLp 2`, mean `m`,
  variance `σ²`, `σ > 0`; conclusion is convergence of the laws of
  `Z_N = (∑(X_i-m))/(σ√N)` to `gaussianReal 0 1`.  This matches Theorem 1.3.2.
- de Moivre–Laplace: `X_i` have law `bernoulliMeasure p`, are independent, and
  `0 < p < 1`; conclusion is the law convergence in (1.7) with
  `σ = sqrt(p(1-p))`.  The added `AEMeasurable` hypothesis is the formal meaning
  of “random variable”, not an extra mathematical assumption.
- `p < 1`: concrete counterexample at `p = 1/2`; this establishes the source's
  “for `p < 1` the triangle inequality fails” by exhibiting one such `p`.
- Poisson: only the two characteristic-function computations are proved; the
  theorem itself remains open.

This is self-review plus kernel checking, not independent semantic review.

## 6. Files changed/added in this continuation

| File | Role |
|---|---|
| `lean/HDP/WeakConvergence.lean` | weak convergence from charFun + tightness |
| `lean/HDP/CharFunTaylor.lean` | second-order charFun expansion |
| `lean/HDP/CLT.lean` | CLT proof |
| `lean/HDP/DeMoivreLaplace.lean` | de Moivre–Laplace corollary |
| `lean/HDP/Sharpness.lean` | `p < 1` counterexample |
| `lean/HDP/PoissonCharFun.lean` | Poisson/Bernoulli charFun foundations |
| `lean/HDP/OpenStatements.lean` | updated status comments; first-attempt target records preserved |
| `reports/coverage-inventory.md` | updated live status |
| `reports/resume-02/*` | this report and axiom evidence |

Existing proofs and statements from the first attempt were preserved; no statement
was weakened.  The `OpenStatements` CLT/de Moivre `Prop` records are superseded by
the actual theorems but retained as evidence of the first attempt.

## 7. Metric snapshot (observational only)

Available exports at the time of writing remain provisional and operator-controlled.
The last read snapshot was `reports/metrics/latest-measurement-summary.json`
(generated 08:15Z): `request_count = 175`, `wall_elapsed_seconds = 1972.972`,
`api_busy_wall_seconds = 685.361`, `known_cost_usd = 0.319346808`; fields not
present remain unknown.  These numbers are not mathematical input.

## 8. Honest final status

Resolved: CLT (1.3.2), de Moivre–Laplace (1.7), and the `p < 1` failure claim.
Open: Poisson limit theorem (1.3.4) — product/log limit and tightness not completed.
The chapter is therefore **not complete**.  No independent review or source-complete
verification is claimed.
