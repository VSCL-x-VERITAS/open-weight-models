import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

private theorem coord_memLp {n : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin n)}
    (hZ : MemLp Z 2 μ) (i : Fin n) : MemLp (fun ω => Z ω i) 2 μ := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).comp_memLp' hZ

private theorem integral_coord {n : ℕ} {Z : Ω → EuclideanSpace ℝ (Fin n)}
    (hZ : MemLp Z 2 μ) (i : Fin n) :
    (∫ ω, Z ω i ∂μ) = (∫ ω, Z ω ∂μ) i := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).integral_comp_comm
    (hZ.integrable (by norm_num))

private theorem integral_norm_sq_coords {n : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin n)) (hZ : MemLp Z 2 μ) :
    (∫ ω, ‖Z ω‖ ^ 2 ∂μ) = ∑ i, ∫ ω, (Z ω i) ^ 2 ∂μ := by
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  exact integral_finset_sum _ (fun i _ => (coord_memLp hZ i).integrable_sq)

/-- Exercise 0.0.3(a): squared Euclidean norm of an independent centered sum. -/
theorem independent_mean_zero_sum_sq {n k : ℕ}
    (Z : Fin k → Ω → EuclideanSpace ℝ (Fin n))
    (hZ : ∀ j, MemLp (Z j) 2 μ)
    (h_indep : iIndepFun Z μ)
    (h_mean : ∀ j, ∫ ω, Z j ω ∂μ = 0) :
    (∫ ω, ‖∑ j, Z j ω‖ ^ 2 ∂μ) =
      ∑ j, ∫ ω, ‖Z j ω‖ ^ 2 ∂μ := by
  have hcoord : ∀ j i, MemLp (fun ω => Z j ω i) 2 μ :=
    fun j i => coord_memLp (hZ j) i
  have hm : ∀ j i, (∫ ω, Z j ω i ∂μ) = 0 := by
    intro j i
    rw [integral_coord (hZ j) i, h_mean j]
    rfl
  have hsum : MemLp (fun ω => ∑ j, Z j ω) 2 μ :=
    memLp_finset_sum _ (fun j _ => hZ j)
  rw [integral_norm_sq_coords _ hsum]
  simp_rw [integral_norm_sq_coords _ (hZ _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : Set.Pairwise (↑(Finset.univ : Finset (Fin k)))
      (fun j l => IndepFun (fun ω => Z j ω i) (fun ω => Z l ω i) μ) := by
    intro j _ l _ hjl
    exact (h_indep.indepFun hjl).comp
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable
  have hv := IndepFun.variance_sum (μ := μ)
    (s := Finset.univ) (fun j _ => hcoord j i) hi
  have hsummean : (∫ ω, (∑ j, Z j ω) i ∂μ) = 0 := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    rw [integral_finset_sum _ (fun j _ => (hcoord j i).integrable (by norm_num))]
    simp [hm]
  have hsumcoord : MemLp (fun ω => (∑ j, Z j ω) i) 2 μ := coord_memLp hsum i
  have hsumeq : (∑ j, fun ω => Z j ω i) = (fun ω => (∑ j, Z j ω) i) := by
    ext ω
    simp only [Finset.sum_apply, WithLp.ofLp_sum]
  rw [hsumeq, variance_of_integral_eq_zero hsumcoord.aemeasurable hsummean] at hv
  simpa only [variance_of_integral_eq_zero (hcoord _ i).aemeasurable (hm _ i)] using hv

/-- Exercise 0.0.3(b): centering subtracts the squared norm of the mean. -/
theorem centered_sq_integral {n : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin n)) (hZ : MemLp Z 2 μ) :
    (∫ ω, ‖Z ω - ∫ ω, Z ω ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - ‖∫ ω, Z ω ∂μ‖ ^ 2 := by
  have hc : MemLp (fun ω => Z ω - ∫ ω, Z ω ∂μ) 2 μ := hZ.sub (memLp_const _)
  rw [integral_norm_sq_coords _ hc, integral_norm_sq_coords Z hZ,
    EuclideanSpace.norm_sq_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hv := variance_eq_sub (coord_memLp hZ i)
  rw [variance_eq_integral (coord_memLp hZ i).aemeasurable] at hv
  simpa only [PiLp.sub_apply, integral_coord hZ i, Real.norm_eq_abs, sq_abs] using hv

end HDP

#print axioms HDP.independent_mean_zero_sum_sq
#print axioms HDP.centered_sq_integral
