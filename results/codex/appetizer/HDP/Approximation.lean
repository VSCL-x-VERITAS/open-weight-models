import Mathlib

open scoped BigOperators InnerProductSpace
open Set

namespace HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A supporting linear functional cannot be strictly positive on all displacements
from a point in the convex hull. -/
theorem exists_nonpos_inner {T : Set E} {x : E} (hx : x ∈ convexHull ℝ T) (v : E) :
    ∃ t ∈ T, ⟪v, t - x⟫_ℝ ≤ 0 := by
  by_contra! h
  have hc : Convex ℝ {t : E | 0 < ⟪v, t - x⟫_ℝ} := by
    intro a ha b hb c d hc hd hcd
    change 0 < ⟪v, c • a + d • b - x⟫_ℝ
    have he : c • a + d • b - x = c • (a - x) + d • (b - x) := by
      calc
        _ = c • a + d • b - (c • x + d • x) := by
          rw [← add_smul, hcd, one_smul]
        _ = _ := by simp only [smul_sub]; abel
    rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    change 0 < ⟪v, a - x⟫_ℝ at ha
    change 0 < ⟪v, b - x⟫_ℝ at hb
    rcases lt_or_eq_of_le hc with hc | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos hc ha) (mul_nonneg hd hb.le)
    · simp_all
  have hp := convexHull_min h hc hx
  change 0 < ⟪v, x - x⟫_ℝ at hp
  simpa using hp

theorem norm_sub_le_of_mem_convexHull {T : Set E} {D : ℝ}
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ D)
    {x t : E} (hx : x ∈ convexHull ℝ T) (ht : t ∈ T) : ‖t - x‖ ≤ D := by
  have hh : T ⊆ Metric.closedBall t D := by
    intro s hs
    simpa [Metric.mem_closedBall, dist_eq_norm] using hdiam s hs t ht
  have hm := convexHull_min hh (convex_closedBall t D) hx
  simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hm

/-- Finite empirical approximation, in unnormalised squared-error form. -/
theorem empirical_sum_bound {T : Set E} {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ D)
    {x : E} (hx : x ∈ convexHull ℝ T) (k : ℕ) :
    ∃ z : Fin k → E, (∀ i, z i ∈ T) ∧
      ‖(∑ i, z i) - (k : ℝ) • x‖ ^ 2 ≤ (k : ℝ) * D ^ 2 := by
  induction k with
  | zero => exact ⟨Fin.elim0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨z, hz, he⟩ := ih
    let v := (∑ i, z i) - (k : ℝ) • x
    obtain ⟨t, ht, hi⟩ := exists_nonpos_inner hx v
    have hn := norm_sub_le_of_mem_convexHull hdiam hx ht
    have hsq : ‖t - x‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (t - x)]
    refine ⟨Fin.cons t z, ?_, ?_⟩
    · intro i
      refine Fin.cases ht (fun j => hz j) i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_add, Nat.cast_one]
      have hv : t + (∑ i, z i) - ((k : ℝ) + 1) • x = v + (t - x) := by
        dsimp [v]
        rw [add_smul, one_smul]
        abel
      rw [hv, norm_add_sq_real]
      change ‖v‖ ^ 2 ≤ (k : ℝ) * D ^ 2 at he
      nlinarith

/-- Theorem 0.0.2, with the footnote's general diameter bound. Repetitions are allowed. -/
theorem approximate_caratheodory {T : Set E} {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ D)
    {x : E} (hx : x ∈ convexHull ℝ T) {k : ℕ} (hk : 0 < k) :
    ∃ z : Fin k → E, (∀ i, z i ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ i, z i‖ ≤ D / Real.sqrt k := by
  obtain ⟨z, hz, he⟩ := empirical_sum_bound hD hdiam hx k
  refine ⟨z, hz, ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkR
  have hss := Real.sq_sqrt hkR.le
  have hn : ‖(∑ i, z i) - (k : ℝ) • x‖ ≤ Real.sqrt k * D := by
    have hp : 0 ≤ Real.sqrt (k : ℝ) * D := mul_nonneg hs.le hD
    nlinarith [sq_nonneg (‖(∑ i, z i) - (k : ℝ) • x‖ - Real.sqrt k * D)]
  have hv : x - (k : ℝ)⁻¹ • ∑ i, z i =
      -( (k : ℝ)⁻¹ • ((∑ i, z i) - (k : ℝ) • x)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hkR.ne', one_smul]
    abel
  rw [hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hkR]
  have hm := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hkR.le)
  have hid : (k : ℝ)⁻¹ * (Real.sqrt k * D) = D / Real.sqrt k := by
    field_simp
    nlinarith
  exact hm.trans_eq hid

end HDP
