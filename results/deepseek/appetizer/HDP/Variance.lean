/-
Exercise 0.0.3: the two variance identities used in the proof of
Theorem 0.0.2.  Part (a) is `integral_norm_sq_sum_of_indep_mean_zero`
in `HDP.FiniteProbability`; part (b) is proved here for a general
probability measure and a square-integrable random vector.
-/
import Mathlib
import HDP.FiniteProbability

open Set BigOperators MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace InnerProductSpace
set_option maxHeartbeats 1000000

namespace HDP

/-- Exercise 0.0.3(b): `E‖Z - E Z‖² = E‖Z‖² - ‖E Z‖²`. -/
theorem variance_identity_vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : Ω → E) (hZ : MemLp Z 2 μ) :
    ∫ ω, ‖Z ω - ∫ ω, Z ω ∂μ‖ ^ 2 ∂μ
      = ∫ ω, ‖Z ω‖ ^ 2 ∂μ - ‖∫ ω, Z ω ∂μ‖ ^ 2 := by
  let m : E := ∫ ω, Z ω ∂μ
  change ∫ ω, ‖Z ω - m‖ ^ 2 ∂μ = ∫ ω, ‖Z ω‖ ^ 2 ∂μ - ‖m‖ ^ 2
  have hZi : Integrable Z μ := hZ.integrable (by norm_num)
  have hZ2 : Integrable (fun ω => ‖Z ω‖ ^ 2) μ := hZ.norm.integrable_sq
  have hinner : Integrable (fun ω => ⟪Z ω, m⟫_ℝ) μ := hZi.inner_const m
  have hconst : Integrable (fun _ : Ω => ‖m‖ ^ 2) μ := integrable_const _
  have hpoint : ∀ ω, ‖Z ω - m‖ ^ 2 = ‖Z ω‖ ^ 2 - 2 * ⟪Z ω, m⟫_ℝ + ‖m‖ ^ 2 := by
    intro ω; rw [norm_sub_sq_real]
  simp_rw [hpoint]
  rw [integral_add (f := fun ω => ‖Z ω‖ ^ 2 - 2 * ⟪Z ω, m⟫_ℝ) (g := fun _ => ‖m‖ ^ 2)
    (hZ2.sub (hinner.const_mul 2)) hconst]
  rw [integral_sub (f := fun ω => ‖Z ω‖ ^ 2) (g := fun ω => 2 * ⟪Z ω, m⟫_ℝ) hZ2
    (hinner.const_mul 2)]
  rw [integral_const_mul, integral_const]
  have hinner_int : ∫ ω, ⟪Z ω, m⟫_ℝ ∂μ = ‖m‖ ^ 2 := by
    rw [show ∫ ω, ⟪Z ω, m⟫_ℝ ∂μ = ∫ ω, ⟪m, Z ω⟫_ℝ ∂μ by
      congr 1 with ω; rw [real_inner_comm]]
    rw [integral_inner hZi m, real_inner_self_eq_norm_sq]
  rw [hinner_int]
  have hμuniv : μ.real univ = 1 := by simp
  rw [hμuniv]
  simp [m]
  ring

end HDP
