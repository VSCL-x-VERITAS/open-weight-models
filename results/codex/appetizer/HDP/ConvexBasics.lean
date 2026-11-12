import Mathlib

open scoped BigOperators
open Finset

namespace HDP

/-- The source's definition of the convex hull as finite convex combinations. -/
theorem mem_convexHull_iff_finite_combination {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : Set E) (x : E) :
    x ∈ convexHull ℝ T ↔ ∃ (s : Finset E) (w : E → ℝ),
      (↑s : Set E) ⊆ T ∧ (∀ z ∈ s, 0 ≤ w z) ∧
      (∑ z ∈ s, w z) = 1 ∧ (∑ z ∈ s, w z • z) = x := by
  rw [convexHull_eq_union_convexHull_finite_subsets]
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨w, hw, hsum, hcombo⟩ := Finset.mem_convexHull'.mp hx
    exact ⟨s, w, hs, hw, hsum, hcombo⟩
  · rintro ⟨s, w, hs, hw, hsum, hcombo⟩
    exact ⟨s, hs, Finset.mem_convexHull'.mpr ⟨w, hw, hsum, hcombo⟩⟩

/-- Theorem 0.0.1, including explicit convex coefficients on at most `n+1` points. -/
theorem caratheodory (n : ℕ) (T : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ convexHull ℝ T) :
    ∃ (s : Finset (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n) → ℝ),
      (↑s : Set (EuclideanSpace ℝ (Fin n))) ⊆ T ∧ s.card ≤ n+1 ∧
      (∀ z ∈ s, 0 ≤ w z) ∧ (∑ z ∈ s, w z) = 1 ∧ (∑ z ∈ s, w z • z) = x := by
  let s := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ha := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hc : s.card ≤ n+1 := by
    have h := ha.card_le_finrank_succ
    have hdim := (vectorSpan ℝ (Set.range ((↑) : s → EuclideanSpace ℝ (Fin n)))).finrank_le
    simp only [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at hdim
    exact h.trans (Nat.add_le_add_right hdim 1)
  obtain ⟨w, hw, hsum, hcombo⟩ := Finset.mem_convexHull'.mp
    (Caratheodory.mem_minCardFinsetOfMemConvexHull hx)
  exact ⟨s, w, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx, hc, hw, hsum, hcombo⟩

/-- A strictly positive combination on a simplex cannot lie in a proper face. -/
theorem positive_simplex_combination_requires_all_vertices {E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : Finset E)
    (ha : AffineIndependent ℝ ((↑) : s → E)) (w : E → ℝ)
    (hw : ∀ z ∈ s, 0 < w z) (hsum : ∑ z ∈ s, w z = 1)
    (t : Finset E) (hts : t ⊆ s)
    (hx : (∑ z ∈ s, w z • z) ∈ convexHull ℝ (↑t : Set E)) : t = s := by
  classical
  obtain ⟨u, hu, husum, hucombo⟩ := Finset.mem_convexHull'.mp hx
  let u' : E → ℝ := fun z => if z ∈ t then u z else 0
  have hsum' : ∑ z ∈ s, u' z = 1 := by
    calc
      ∑ z ∈ s, u' z = ∑ z ∈ t, u' z :=
        (sum_subset hts (by intro z _ hz; simp [u', hz])).symm
      _ = 1 := by simpa [u'] using husum
  have hcombo' : ∑ z ∈ s, u' z • z = ∑ z ∈ s, w z • z := by
    calc
      ∑ z ∈ s, u' z • z = ∑ z ∈ t, u' z • z :=
        (sum_subset hts (by intro z _ hz; simp [u', hz])).symm
      _ = ∑ z ∈ s, w z • z := by simpa [u'] using hucombo
  have heq := ha.eq_of_sum_eq_sum_subtype (hsum.trans hsum'.symm) hcombo'.symm
  apply Subset.antisymm hts
  intro z hz
  by_contra hzt
  have hz0 : w z = 0 := by simpa [u', hzt] using heq z hz
  exact (hw z hz).ne' hz0

/-- In every dimension the `n+1` in Carathéodory's theorem is attained by a simplex. -/
theorem caratheodory_sharp (n : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin n)), s.card = n+1 ∧
      AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n)) ∧
      ∃ x, x ∈ convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) ∧
        ∀ t : Finset (EuclideanSpace ℝ (Fin n)), t ⊆ s →
          x ∈ convexHull ℝ (↑t : Set (EuclideanSpace ℝ (Fin n))) → n+1 ≤ t.card := by
  classical
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (k := ℝ) (V := EuclideanSpace ℝ (Fin n)) (P := EuclideanSpace ℝ (Fin n))
    (ι := Fin (n+1)) (by simp)
  let s : Finset (EuclideanSpace ℝ (Fin n)) := univ.image b
  have hs : (↑s : Set (EuclideanSpace ℝ (Fin n))) = Set.range b := by
    ext z
    simp [s]
  have hcard : s.card = n+1 := by
    dsimp [s]
    rw [card_image_of_injective _ b.ind.injective]
    simp
  have ha : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n)) := by
    have hb := b.ind.range
    rw [← hs] at hb
    exact hb
  let w : EuclideanSpace ℝ (Fin n) → ℝ := fun _ => 1 / (s.card : ℝ)
  have hpos : (0 : ℝ) < s.card := by rw [hcard]; positivity
  have hw : ∀ z ∈ s, 0 < w z := by intro z _; exact one_div_pos.mpr hpos
  have hsum : ∑ z ∈ s, w z = 1 := by simp [w, hpos.ne']
  refine ⟨s, hcard, ha, ∑ z ∈ s, w z • z, ?_, ?_⟩
  · exact Finset.mem_convexHull'.mpr ⟨w, fun z hz => (hw z hz).le, hsum, rfl⟩
  · intro t hts hx
    have ht := positive_simplex_combination_requires_all_vertices s ha w hw hsum t hts hx
    rw [ht, hcard]

#print axioms mem_convexHull_iff_finite_combination
#print axioms caratheodory
#print axioms positive_simplex_combination_requires_all_vertices
#print axioms caratheodory_sharp
end HDP
