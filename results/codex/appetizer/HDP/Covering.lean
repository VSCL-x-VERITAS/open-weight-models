import HDP.Approximation
import HDP.Combinatorics

open scoped BigOperators
open Set
namespace HDP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite family of closed balls of radius `ε` covers `P`. -/
def BallCover (P : Set E) (ε : ℝ) (C : Finset E) : Prop :=
  ∀ x ∈ P, ∃ c ∈ C, x ∈ Metric.closedBall c ε

/-- All means of ordered samples, with repetition allowed. -/
noncomputable def orderedCenters (V : Finset E) (k : ℕ) : Finset E := by
  classical
  exact Finset.univ.image (fun z : Fin k → ↥V => (k : ℝ)⁻¹ • ∑ i, (z i : E))

/-- The same means represented using unordered samples. -/
noncomputable def unorderedCenters (V : Finset E) (k : ℕ) : Finset E := by
  classical
  exact Finset.univ.image (fun s : Sym ↥V k =>
    (k : ℝ)⁻¹ • ((s : Multiset ↥V).map (fun v => (v : E))).sum)

lemma orderedCenters_card (V : Finset E) (k : ℕ) :
    (orderedCenters V k).card ≤ V.card ^ k := by
  classical
  calc
    _ ≤ Fintype.card (Fin k → ↥V) := Finset.card_image_le
    _ = _ := by simp

lemma unorderedCenters_card (V : Finset E) (k : ℕ) :
    (unorderedCenters V k).card ≤ (V.card+k-1).choose k := by
  classical
  calc
    _ ≤ Fintype.card (Sym ↥V k) := Finset.card_image_le
    _ = _ := by simpa using (Sym.card_sym_eq_choose (α := ↥V) k)

lemma orderedCenters_subset_unorderedCenters (V : Finset E) (k : ℕ) :
    orderedCenters V k ⊆ unorderedCenters V k := by
  classical
  intro c hc
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hc
  let s : Sym ↥V k := ⟨(List.ofFn z : Multiset ↥V), by simp⟩
  apply Finset.mem_image.mpr
  refine ⟨s, Finset.mem_univ _, ?_⟩
  simp [s, Multiset.map_coe, List.map_ofFn, List.sum_ofFn]

lemma ceiling_sample_size (ε : ℝ) (hε : 0 < ε) :
    0 < ⌈1/ε^2⌉₊ ∧ 1 ≤ ε^2 * (⌈1/ε^2⌉₊ : ℝ) ∧
    1 / Real.sqrt (⌈1/ε^2⌉₊ : ℝ) ≤ ε := by
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hk : 0 < ⌈1/ε^2⌉₊ := Nat.one_le_ceil_iff.mpr (div_pos zero_lt_one he2)
  have hceil := Nat.le_ceil (1/ε^2)
  have hprod : 1 ≤ ε^2 * (⌈1/ε^2⌉₊ : ℝ) := by
    exact (div_le_iff₀ he2).mp hceil |>.trans_eq (mul_comm _ _)
  refine ⟨hk, hprod, ?_⟩
  have hkR : (0 : ℝ) < ⌈1/ε^2⌉₊ := by exact_mod_cast hk
  have hs := Real.sqrt_pos.mpr hkR
  apply (div_le_iff₀ hs).mpr
  have hss := Real.sq_sqrt hkR.le
  have hsq : (ε * Real.sqrt (⌈1/ε^2⌉₊ : ℝ))^2 =
      ε^2 * (⌈1/ε^2⌉₊ : ℝ) := by rw [mul_pow, hss]
  nlinarith [mul_pos hε hs]

lemma orderedCenters_cover (V : Finset E) (ε : ℝ) (hε : 0 < ε)
    (hdiam : ∀ s ∈ convexHull ℝ (V : Set E),
      ∀ t ∈ convexHull ℝ (V : Set E), ‖s-t‖ ≤ 1) :
    BallCover (convexHull ℝ (V : Set E)) ε (orderedCenters V ⌈1/ε^2⌉₊) := by
  classical
  intro x hx
  have hvdiam : ∀ s ∈ (V : Set E), ∀ t ∈ (V : Set E), ‖s-t‖ ≤ (1 : ℝ) := by
    intro s hs t ht
    exact hdiam s (subset_convexHull ℝ (V : Set E) hs)
      t (subset_convexHull ℝ (V : Set E) ht)
  obtain ⟨hk, -, he⟩ := ceiling_sample_size ε hε
  obtain ⟨z, hz, hb⟩ := approximate_caratheodory zero_le_one hvdiam hx hk
  let z' : Fin ⌈1/ε^2⌉₊ → ↥V := fun i => ⟨z i, hz i⟩
  refine ⟨_, Finset.mem_image.mpr ⟨z', Finset.mem_univ _, rfl⟩, ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm, z'] using hb.trans he

/-- Corollary 0.0.4, exposing the finite vertex set through its convex hull. -/
theorem covering_polytopes (V : Finset E) (ε : ℝ) (hε : 0 < ε)
    (hdiam : ∀ s ∈ convexHull ℝ (V : Set E),
      ∀ t ∈ convexHull ℝ (V : Set E), ‖s-t‖ ≤ 1) :
    ∃ C : Finset E, BallCover (convexHull ℝ (V : Set E)) ε C ∧
      C.card ≤ V.card ^ ⌈1/ε^2⌉₊ :=
  ⟨_, orderedCenters_cover V ε hε hdiam, orderedCenters_card V _⟩

/-- Exercise 0.0.6 with the explicit absolute constant `C = exp 1`. -/
theorem improved_covering (V : Finset E) (ε : ℝ) (hε : 0 < ε)
    (hdiam : ∀ s ∈ convexHull ℝ (V : Set E),
      ∀ t ∈ convexHull ℝ (V : Set E), ‖s-t‖ ≤ 1) :
    ∃ C : Finset E, BallCover (convexHull ℝ (V : Set E)) ε C ∧
      C.card ≤ (V.card + ⌈1/ε^2⌉₊ - 1).choose ⌈1/ε^2⌉₊ ∧
      (C.card : ℝ) ≤ (Real.exp 1 + Real.exp 1 * ε^2 * V.card)^⌈1/ε^2⌉₊ := by
  refine ⟨unorderedCenters V ⌈1/ε^2⌉₊, ?_, unorderedCenters_card V _, ?_⟩
  · intro x hx
    obtain ⟨c, hc, hd⟩ := orderedCenters_cover V ε hε hdiam x hx
    exact ⟨c, orderedCenters_subset_unorderedCenters V _ hc, hd⟩
  · have hc : ((unorderedCenters V ⌈1/ε^2⌉₊).card : ℝ) ≤
        ((V.card + ⌈1/ε^2⌉₊ - 1).choose ⌈1/ε^2⌉₊ : ℝ) := by
      exact Nat.cast_le.mpr (unorderedCenters_card V ⌈1/ε^2⌉₊)
    exact hc.trans (unordered_selection_epsilon_bound V.card _
      (ceiling_sample_size ε hε).1 ε (ceiling_sample_size ε hε).2.1)

#print axioms covering_polytopes
#print axioms improved_covering
end HDP
