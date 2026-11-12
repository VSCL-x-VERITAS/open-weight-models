/-
Section 1.2, first part: Jensen's inequality, monotonicity of `L^p` norms in `p`,
Minkowski's inequality, the Cauchy--Schwarz inequality and Hölder's inequality.

The source states these for random variables; we use Mathlib's measure-theoretic
versions and record the correspondence in the docstrings.
-/
import Mathlib
import HDP.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

/-- Jensen's inequality: for a convex `φ : ℝ → ℝ` and integrable `X`, `φ (E X) ≤ E (φ ∘ X)`. -/
theorem jensen [IsProbabilityMeasure μ] {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ) :
    φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ := by
  have hcont : ContinuousOn φ Set.univ := hφ.continuousOn isOpen_univ
  exact hφ.map_integral_le hcont isClosed_univ (by simp) hX hφX

/-- Inequality (1.3): `‖X‖_{L^p} ≤ ‖X‖_{L^q}` for `0 ≤ p ≤ q ≤ ∞` on a probability space. -/
theorem LpNorm_mono [IsProbabilityMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hX : AEStronglyMeasurable X μ) : LpNorm p μ X ≤ LpNorm q μ X :=
  eLpNorm_le_eLpNorm_of_exponent_le hpq hX

/-- Minkowski's inequality (1.4), in `ℝ≥0∞`-valued form. -/
theorem LpNorm_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hX : MemLp X p μ) (hY : MemLp Y p μ) :
    LpNorm p μ (X + Y) ≤ LpNorm p μ X + LpNorm p μ Y :=
  eLpNorm_add_le hX.1 hY.1 hp

/-- Hölder's inequality for conjugate exponents `p, q ∈ (1, ∞)`; the case `p = 1`,
`q = ∞` is `holder_one_top` below. -/
theorem holder {p q : ℝ} (hpq : p.HolderConjugate q)
    (hX : MemLp X (ENNReal.ofReal p) μ) (hY : MemLp Y (ENNReal.ofReal q) μ) :
    |∫ ω, X ω * Y ω ∂μ| ≤ lpNorm X (ENNReal.ofReal p) μ * lpNorm Y (ENNReal.ofReal q) μ := by
  have hp0 : p ≠ 0 := hpq.pos.ne'
  have hq0 : q ≠ 0 := hpq.symm.pos.ne'
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hmain := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hpq hX hY
  calc
    |∫ ω, X ω * Y ω ∂μ| ≤ ∫ ω, ‖X ω * Y ω‖ ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, ‖X ω‖ * ‖Y ω‖ ∂μ := by simp [norm_mul]
    _ ≤ (∫ ω, ‖X ω‖ ^ p ∂μ) ^ (1 / p) * (∫ ω, ‖Y ω‖ ^ q ∂μ) ^ (1 / q) := hmain
    _ = lpNorm X (ENNReal.ofReal p) μ * lpNorm Y (ENNReal.ofReal q) μ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne' hp_top hX.1,
        lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne' hq_top hY.1]
      simp [ENNReal.toReal_ofReal hpq.pos.le, ENNReal.toReal_ofReal hpq.symm.pos.le]

/-- Hölder's inequality in the case `p = 1`, `q = ∞`. -/
theorem holder_one_top [IsProbabilityMeasure μ] (hX : MemLp X 1 μ) (hY : MemLp Y ∞ μ) :
    |∫ ω, X ω * Y ω ∂μ| ≤ lpNorm X 1 μ * lpNorm Y ∞ μ := by
  have hXint : Integrable X μ := memLp_one_iff_integrable.mp hX
  have hYabs_meas : AEStronglyMeasurable (fun ω => |Y ω|) μ := by
    simpa [Real.norm_eq_abs] using hY.1.norm
  have hXYint : Integrable (fun ω => |X ω| * |Y ω|) μ := by
    apply hXint.abs.mul_bdd (c := lpNorm Y ∞ μ) hYabs_meas
    filter_upwards [ae_le_lpNorm_exponent_top hY] with ω h
    simpa [Real.norm_eq_abs] using h
  calc
    |∫ ω, X ω * Y ω ∂μ| ≤ ∫ ω, |X ω * Y ω| ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, |X ω| * |Y ω| ∂μ := by simp [abs_mul]
    _ ≤ ∫ ω, |X ω| * lpNorm Y ∞ μ ∂μ := by
      apply integral_mono_ae hXYint (hXint.abs.mul_const _)
      filter_upwards [ae_le_lpNorm_exponent_top hY] with ω h
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using h) (abs_nonneg _)
    _ = (∫ ω, |X ω| ∂μ) * lpNorm Y ∞ μ := by rw [integral_mul_const]
    _ = lpNorm X 1 μ * lpNorm Y ∞ μ := by
      rw [show (∫ ω, |X ω| ∂μ) = ∫ ω, ‖X ω‖ ∂μ by simp [Real.norm_eq_abs]]
      rw [lpNorm_one_eq_integral_norm hX.1]

/-- Cauchy--Schwarz is Hölder with `p = q = 2`. -/
theorem cauchy_schwarz (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ ω, X ω * Y ω ∂μ| ≤ lpNorm X 2 μ * lpNorm Y 2 μ := by
  simpa using holder (μ := μ) (X := X) (Y := Y) (p := 2) (q := 2)
    (Real.HolderConjugate.two_two) (by simpa using hX) (by simpa using hY)

end HDP
