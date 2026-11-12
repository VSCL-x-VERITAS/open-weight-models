import HDP.Approximation

open scoped BigOperators
open Set

namespace HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The translation used before (0.2). -/
theorem translate_radius_bound {T : Set E} {D : ℝ}
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ D) {a : E} (ha : a ∈ T) :
    ∀ u ∈ (fun t => t - a) '' T, ‖u‖ ≤ D := by
  rintro u ⟨t, ht, rfl⟩
  exact hdiam t ht a ha

theorem translation_preserves_distance (s t a : E) :
    ‖(s - a) - (t - a)‖ = ‖s - t‖ := by
  congr 1
  abel

theorem translate_mem_convexHull {T : Set E} {x : E}
    (hx : x ∈ convexHull ℝ T) (a : E) :
    x - a ∈ convexHull ℝ ((fun t => t - a) '' T) := by
  obtain ⟨ι, hι, w, z, hw, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  letI := hι
  apply mem_convexHull_of_exists_fintype w (fun i => z i - a) hw hw1
  · intro i
    exact ⟨z i, hz i, rfl⟩
  · simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul, hx]

theorem translation_preserves_mean_error {k : ℕ} (hk : 0 < k)
    (z : Fin k → E) (x a : E) :
    (x - a) - (k : ℝ)⁻¹ • (∑ i, (z i - a)) = x - (k : ℝ)⁻¹ • ∑ i, z i := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hkR, one_smul]
  abel

theorem approximate_caratheodory_diam {T : Set E} (hT : Bornology.IsBounded T)
    {x : E} (hx : x ∈ convexHull ℝ T) {k : ℕ} (hk : 0 < k) :
    ∃ z : Fin k → E, (∀ i, z i ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ i, z i‖ ≤ Metric.diam T / Real.sqrt k := by
  apply approximate_caratheodory Metric.diam_nonneg ?_ hx hk
  intro s hs t ht
  simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem hT hs ht

/-- On nonempty bounded sets, Mathlib's diameter is precisely the source supremum. -/
theorem diameter_eq_sup {T : Set E} (hne : T.Nonempty) (hT : Bornology.IsBounded T) :
    Metric.diam T = sSup {r : ℝ | ∃ s ∈ T, ∃ t ∈ T, r = ‖s - t‖} := by
  let S : Set ℝ := {r | ∃ s ∈ T, ∃ t ∈ T, r = ‖s - t‖}
  obtain ⟨a, ha⟩ := hne
  have hzero : (0 : ℝ) ∈ S := ⟨a, ha, a, ha, by simp⟩
  have hS : S.Nonempty := ⟨0, hzero⟩
  have hbound : BddAbove S := by
    refine ⟨Metric.diam T, ?_⟩
    rintro r ⟨s, hs, t, ht, rfl⟩
    simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem hT hs ht
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (le_csSup hbound hzero)
    intro s hs t ht
    simpa [dist_eq_norm] using (le_csSup hbound (show ‖s - t‖ ∈ S from ⟨s, hs, t, ht, rfl⟩))
  · apply csSup_le hS
    rintro r ⟨s, hs, t, ht, rfl⟩
    simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem hT hs ht

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- A finite convex hull has finitely many vertices and is their convex hull. -/
theorem polytope_vertices {P : Set E}
    (hP : ∃ V : Finset E, P = convexHull ℝ (V : Set E)) :
    (P.extremePoints ℝ).Finite ∧ convexHull ℝ (P.extremePoints ℝ) = P := by
  obtain ⟨V, rfl⟩ := hP
  have hv : ((convexHull ℝ (V : Set E)).extremePoints ℝ).Finite :=
    V.finite_toSet.subset extremePoints_convexHull_subset
  refine ⟨hv, ?_⟩
  have hc := closure_convexHull_extremePoints (V.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (V : Set E))
  rwa [(hv.isClosed_convexHull ℝ).closure_eq] at hc

end FiniteDimensional

/-- The source's small-radius comparison is meaningful when N exceeds the absolute constant. -/
theorem improved_base_eventually_smaller (N : ℕ) (hN : Real.exp 1 < (N : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Real.exp 1 + Real.exp 1 * ε ^ 2 * N < N := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hn : (0 : ℝ) < N := he.trans hN
  let q : ℝ := ((N : ℝ) - Real.exp 1) / (Real.exp 1 * N)
  have hq : 0 < q := div_pos (sub_pos.mpr hN) (mul_pos he hn)
  refine ⟨Real.sqrt q, Real.sqrt_pos.mpr hq, ?_⟩
  intro ε hε hεδ
  have hs := Real.sq_sqrt hq.le
  have hεq : ε ^ 2 < q := by nlinarith [Real.sqrt_nonneg q]
  have hprod : ε ^ 2 * (Real.exp 1 * N) < (N : ℝ) - Real.exp 1 :=
    (lt_div_iff₀ (mul_pos he hn)).mp hεq
  nlinarith

end HDP
