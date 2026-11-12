/-
Chapter 1 of the source: basic quantities associated with random variables.

The definitions below mirror the source's notation.  Where Mathlib already has the
corresponding notion (`variance`, `covariance`, `mgf`, `eLpNorm`, `cdf`, ...) we use
that notion directly and record the source correspondence in comments; the small
wrappers are only for names that Mathlib does not provide.
-/
import Mathlib

/-! ### Basic quantities -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Expectation of a real random variable, written `E X` in the source. -/
noncomputable def expectation (μ : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

/-- The empirical average `(X_0 + ... + X_{N-1}) / N` from Section 1.3. -/
noncomputable def sampleMean (X : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℝ :=
  fun ω => (∑ i ∈ Finset.range N, X i ω) / (N : ℝ)

/-- The `L^p` norm, written `‖X‖_{L^p}` in the source.  This is Mathlib's `eLpNorm`;
for `p = ∞` it is the essential supremum of `‖X‖`. -/
noncomputable def LpNorm (p : ℝ≥0∞) (μ : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ :=
  eLpNorm X p μ

/-- The `L^p` space of real random variables with finite `L^p` norm. -/
def LpSpace (p : ℝ≥0∞) (μ : Measure Ω) : Set (Ω → ℝ) :=
  {X | MemLp X p μ}

/-- The `L^2` inner product `⟨X, Y⟩_{L^2} = E[XY]` from (1.1). -/
noncomputable def l2Inner (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ := ∫ ω, X ω * Y ω ∂μ

/-- Standard deviation `σ(X) = sqrt (Var X)`. -/
noncomputable def stdDev (μ : Measure Ω) (X : Ω → ℝ) : ℝ := Real.sqrt (variance X μ)

/-- The `p`-th absolute moment `E |X|^p`. -/
noncomputable def absMoment (p : ℝ) (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, |X ω| ^ p ∂μ

/-- The `p`-th moment `E X^p` (for real exponent this is the real power). -/
noncomputable def moment (p : ℝ) (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ^ p ∂μ

/-- Cumulative distribution function `F_X(t) = P(X ≤ t)` of a real random variable. -/
noncomputable def cdfOf (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  cdf (μ.map X) t

/-- The upper tail probability `P(X > t)`. -/
noncomputable def tail (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.real {ω | t < X ω}

/-- Convergence in distribution, as weak convergence of the laws. -/
def ConvergesInDistribution (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (Z : Ω → ℝ) : Prop :=
  MeasureTheory.TendstoInDistribution X Filter.atTop Z μ

end HDP

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

/-- The covariance is the `L^2` inner product of the centered variables, formula (1.2). -/
theorem covariance_eq_l2Inner :
    cov[X, Y; μ] = l2Inner μ (fun ω => X ω - μ[X]) (fun ω => Y ω - μ[Y]) := rfl

/-- The `L^2` inner product of a variable with itself. -/
theorem l2Inner_self (X : Ω → ℝ) : l2Inner μ X X = ∫ ω, X ω ^ 2 ∂μ := by
  simp [l2Inner, pow_two]

/-- The standard deviation is the `L^2` norm of the centered variable. -/
theorem stdDev_eq_lpNorm [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) :
    stdDev μ X = lpNorm (fun ω => X ω - μ[X]) 2 μ := by
  have h2 : MemLp (fun ω => X ω - μ[X]) 2 μ := hX.sub (memLp_const _)
  rw [stdDev, variance_eq_integral hX.aemeasurable]
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num) h2.1]
  rw [Real.sqrt_eq_rpow]
  have hexp : (ENNReal.toReal 2)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hexp]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  simp [Real.norm_eq_abs, sq_abs]


/-- The moment generating function `M_X(t) = E e^{tX}` from Section 1.1. -/
noncomputable def mgfOf (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ := mgf X μ t

/-- Unfolding of the moment generating function as an expectation. -/
theorem mgfOf_eq_integral (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    mgfOf μ X t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl

end HDP
