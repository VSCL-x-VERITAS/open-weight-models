import HDP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IndependentAudit
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

theorem expectation_default (h : ¬ Integrable X μ) : HDP.expectation μ X = 0 := by
  exact integral_undef h

theorem mgf_default {t : ℝ}
    (h : ¬ Integrable (fun ω => Real.exp (t * X ω)) μ) :
    HDP.mgfOf μ X t = 0 := by
  exact mgf_undef h

theorem variance_default [IsFiniteMeasure μ]
    (hm : AEStronglyMeasurable X μ) (h : ¬ MemLp X 2 μ) :
    variance X μ = 0 := variance_of_not_memLp hm h

theorem extended_variance_infinite [IsFiniteMeasure μ]
    (hm : AEStronglyMeasurable X μ) (h : ¬ MemLp X 2 μ) :
    evariance X μ = ∞ := (evariance_eq_top_iff hm).mpr h

#print axioms expectation_default
#print axioms mgf_default
#print axioms variance_default
#print axioms extended_variance_infinite

theorem negative_third_power_convention : (-1 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by
  rw [Real.rpow_def_of_neg (by norm_num : (-1 : ℝ) < 0)]
  norm_num
  convert Real.cos_pi_div_three using 1 <;> congr 1 <;> ring

theorem constant_negative_moment :
    HDP.moment (1 / 3) (Measure.dirac ()) (fun _ : Unit => (-1 : ℝ)) = 1 / 2 := by
  simpa [HDP.moment] using negative_third_power_convention

#print axioms negative_third_power_convention
#print axioms constant_negative_moment
end IndependentAudit
