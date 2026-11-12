/-
The explanatory claim in Section 1.1 that for `p < 1` the triangle inequality
fails and `‖·‖_{L^p}` is not a norm.  We give a concrete counterexample on a
two-point probability space for `p = 1/2`.
-/
import Mathlib
import HDP.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HDP

/-- The value `1/2`, as an `ℝ≥0∞`. -/
noncomputable abbrev half : ℝ≥0∞ := ((1/2 : ℝ≥0) : ℝ≥0∞)

/-- The uniform probability measure on `Bool`. -/
noncomputable def coin : Measure Bool :=
  half • Measure.dirac true + half • Measure.dirac false

instance coin_isProbability : IsProbabilityMeasure coin := by
  constructor
  rw [coin, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  simp only [Set.indicator_of_mem, Set.mem_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [show half + half = (1 : ℝ≥0∞) by
    rw [show half = ((1/2 : ℝ≥0) : ℝ≥0∞) from rfl, ← ENNReal.coe_add]
    norm_num
    rfl]

/-- Indicator of the point `true`. -/
def coinX : Bool → ℝ := fun b => if b then 1 else 0

/-- Indicator of the point `false`. -/
def coinY : Bool → ℝ := fun b => if b then 0 else 1

lemma coin_integral_X : ∫ x, |coinX x| ^ ((1/2 : ℝ≥0) : ℝ) ∂coin = 1/2 := by
  rw [coin, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    norm_num [coinX]
    rfl
  · exact (integrable_dirac (a := true)
      (f := fun x : Bool => |coinX x| ^ ((1/2 : ℝ≥0) : ℝ)) (by simp [coinX])).smul_measure (by simp)
  · exact (integrable_dirac (a := false)
      (f := fun x : Bool => |coinX x| ^ ((1/2 : ℝ≥0) : ℝ)) (by simp [coinX])).smul_measure (by simp)

lemma coin_integral_Y : ∫ x, |coinY x| ^ ((1/2 : ℝ≥0) : ℝ) ∂coin = 1/2 := by
  rw [coin, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    norm_num [coinY]
    rfl
  · exact (integrable_dirac (a := true)
      (f := fun x : Bool => |coinY x| ^ ((1/2 : ℝ≥0) : ℝ)) (by simp [coinY])).smul_measure (by simp)
  · exact (integrable_dirac (a := false)
      (f := fun x : Bool => |coinY x| ^ ((1/2 : ℝ≥0) : ℝ)) (by simp [coinY])).smul_measure (by simp)

lemma coin_integral_XY : ∫ x, |(coinX + coinY) x| ^ ((1/2 : ℝ≥0) : ℝ) ∂coin = 1 := by
  rw [coin, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    norm_num [coinX, coinY]
  · exact (integrable_dirac (a := true)
      (f := fun x : Bool => |(coinX + coinY) x| ^ ((1/2 : ℝ≥0) : ℝ)) (by simp [coinX, coinY])).smul_measure (by simp)
  · exact (integrable_dirac (a := false)
      (f := fun x : Bool => |(coinX + coinY) x| ^ ((1/2 : ℝ≥0) : ℝ)) (by simp [coinX, coinY])).smul_measure (by simp)

/-- The `L^{1/2}` norm of `coinX` is `1/4`. -/
theorem coin_lpNorm_X : lpNorm coinX half coin = 1/4 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := half) (by norm_num) (by norm_num) (by fun_prop)]
  simp only [half, ENNReal.coe_toReal]
  rw [show (∫ x, ‖coinX x‖ ^ ((1/2 : ℝ≥0) : ℝ) ∂coin) =
      ∫ x, |coinX x| ^ ((1/2 : ℝ≥0) : ℝ) ∂coin by simp [Real.norm_eq_abs]]
  rw [coin_integral_X]
  have hp : (((1/2 : ℝ≥0) : ℝ))⁻¹ = (2:ℝ) := by
    norm_num
    rfl
  rw [hp, Real.rpow_two]
  norm_num

/-- The `L^{1/2}` norm of `coinY` is `1/4`. -/
theorem coin_lpNorm_Y : lpNorm coinY half coin = 1/4 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := half) (by norm_num) (by norm_num) (by fun_prop)]
  simp only [half, ENNReal.coe_toReal]
  rw [show (∫ x, ‖coinY x‖ ^ ((1/2 : ℝ≥0) : ℝ) ∂coin) =
      ∫ x, |coinY x| ^ ((1/2 : ℝ≥0) : ℝ) ∂coin by simp [Real.norm_eq_abs]]
  rw [coin_integral_Y]
  have hp : (((1/2 : ℝ≥0) : ℝ))⁻¹ = (2:ℝ) := by
    norm_num
    rfl
  rw [hp, Real.rpow_two]
  norm_num

/-- The `L^{1/2}` norm of `coinX + coinY` is `1`. -/
theorem coin_lpNorm_XY : lpNorm (coinX + coinY) half coin = 1 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := half) (by norm_num) (by norm_num) (by fun_prop)]
  simp only [half, ENNReal.coe_toReal]
  rw [show (∫ x, ‖(coinX + coinY) x‖ ^ ((1/2 : ℝ≥0) : ℝ) ∂coin) =
      ∫ x, |(coinX + coinY) x| ^ ((1/2 : ℝ≥0) : ℝ) ∂coin by simp [Real.norm_eq_abs]]
  rw [coin_integral_XY]
  have hp : (((1/2 : ℝ≥0) : ℝ))⁻¹ = (2:ℝ) := by
    norm_num
    rfl
  rw [hp, Real.rpow_two]
  norm_num

/-- For `p = 1/2 < 1` the triangle inequality fails:
`‖X + Y‖_{L^{1/2}} = 1` while `‖X‖_{L^{1/2}} + ‖Y‖_{L^{1/2}} = 1/2`. -/
theorem triangle_inequality_fails_at_half :
    ¬ lpNorm (coinX + coinY) half coin ≤
      lpNorm coinX half coin + lpNorm coinY half coin := by
  rw [coin_lpNorm_XY, coin_lpNorm_X, coin_lpNorm_Y]
  norm_num

end HDP
