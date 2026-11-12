/-
Records of the Section 1.3 limit-theorem statements.

**Status after RESUME_02.**  The Lindeberg--Lévy CLT (Theorem 1.3.2) is now proved in
`HDP.CLT` as `HDP.central_limit_theorem`, and the de Moivre--Laplace theorem (1.7) is
proved in `HDP.DeMoivreLaplace` as `HDP.de_moivre_laplace`.  The `Prop` definitions
below for those two statements are kept only as the first-attempt target record.

The Poisson limit theorem (Theorem 1.3.4) is still **not proved**.  Its exact
triangular-array statement is recorded as `PoissonLimitTheorem`; the Poisson and
Bernoulli characteristic functions used toward it are proved in
`HDP.PoissonCharFun`.
-/
import Mathlib
import HDP.Basic
import HDP.LimitTheorems

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory BigOperators Function Topology

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The i.i.d. hypothesis used by the limit theorems, stated with Mathlib's
`IdentDistrib` and pairwise independence. -/
def IsIID [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) : Prop :=
  (∀ i, AEMeasurable (X i) μ) ∧
    (∀ i, IdentDistrib (X i) (X 0) μ μ) ∧
    Pairwise ((· ⟂ᵢ[μ] ·) on X)

/-- The conclusion of the Lindeberg--Lévy CLT, in the CDF form used in the source:
the normalized sums have CDFs converging pointwise to the standard normal CDF. -/
def CLTConclusion [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop :=
  ∀ t : ℝ,
    Tendsto
      (fun N : ℕ =>
        (μ.map (fun ω =>
          (∑ i ∈ Finset.range N, (X i ω - m)) / (σ * Real.sqrt (N : ℝ)))).real
          (Set.Iic t))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic t)))

/-- Theorem 1.3.2 (Lindeberg--Lévy central limit theorem), recorded as a proposition:
i.i.d. variables with mean `m` and variance `σ^2 > 0` satisfy the CLT. -/
def CentralLimitTheorem [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) : Prop :=
  IsIID (μ := μ) X →
    (∀ i, Integrable (X i) μ) →
    (∀ i, ∫ ω, X i ω ∂μ = m) →
    (∀ i, variance (X i) μ = σ ^ 2) →
    0 < σ → CLTConclusion (μ := μ) X m σ

/-- Formula (1.7), the de Moivre--Laplace theorem: the Bernoulli special case of the CLT. -/
def DeMoivreLaplaceTheorem [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (p : ℝ≥0)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) : Prop :=
  (∀ i, μ.map (X i) = bernoulliMeasure p) →
    Pairwise ((· ⟂ᵢ[μ] ·) on X) →
    ∀ t : ℝ,
      Tendsto
        (fun N : ℕ =>
          (μ.map (fun ω =>
            ((∑ i ∈ Finset.range N, X i ω) - (N : ℝ) * (p : ℝ)) /
              Real.sqrt ((N : ℝ) * (p : ℝ) * (1 - (p : ℝ))))).real (Set.Iic t))
        atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic t)))

/-- Theorem 1.3.4 (Poisson limit theorem), recorded as a proposition.  `X N i` are
the `i`-th Bernoulli variable of the `N`-th row, with parameters `p N i`. -/
def PoissonLimitTheorem [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ)
    (p : ℕ → ℕ → ℝ≥0) (hp : ∀ N i, p N i ≤ 1) (lam : ℝ≥0) : Prop :=
  (∀ N i, i < N → μ.map (X N i) = bernoulliMeasure (p N i)) →
    (∀ N, Set.Pairwise {i : ℕ | i < N} fun i j => X N i ⟂ᵢ[μ] X N j) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i < N, (p N i : ℝ) < ε) →
    Tendsto (fun N => ∑ i ∈ Finset.range N, (p N i : ℝ)) atTop (𝓝 (lam : ℝ)) →
    ∀ k : ℕ,
      Tendsto
        (fun N : ℕ =>
          (μ.map (fun ω => ∑ i ∈ Finset.range N, X N i ω)).real (Set.Iic k))
        atTop (𝓝 ((poissonDist lam).real (Set.Iic k)))

end HDP
