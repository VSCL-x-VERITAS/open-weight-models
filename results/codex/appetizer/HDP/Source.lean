import HDP.ConvexBasics
import HDP.Covering
import HDP.Empirical
import HDP.Supplemental

open scoped BigOperators
open Set

namespace HDP.Source

/-- Theorem 0.0.2 with its exact unit diameter and Euclidean ambient space. -/
theorem theorem_0_0_2 {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n)))
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ T)
    {k : ℕ} (hk : 0 < k) :
    ∃ z : Fin k → EuclideanSpace ℝ (Fin n), (∀ i, z i ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ i, z i‖ ≤ 1 / Real.sqrt k :=
  HDP.approximate_caratheodory zero_le_one hdiam hx hk

/-- Corollary 0.0.4 counts actual extreme vertices of the polytope. -/
theorem corollary_0_0_4 {n N : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP : ∃ V : Finset (EuclideanSpace ℝ (Fin n)), P = convexHull ℝ (V : Set _))
    (hN : (P.extremePoints ℝ).ncard = N)
    (hdiam : ∀ s ∈ P, ∀ t ∈ P, ‖s - t‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin n)), HDP.BallCover P ε C ∧
      C.card ≤ N ^ ⌈1 / ε ^ 2⌉₊ := by
  classical
  obtain ⟨hv, hh⟩ := HDP.polytope_vertices hP
  let V := hv.toFinset
  have hV : (V : Set (EuclideanSpace ℝ (Fin n))) = P.extremePoints ℝ := hv.coe_toFinset
  have hVP : convexHull ℝ (V : Set _) = P := by rw [hV, hh]
  have hcard : V.card = N := by
    rw [Set.ncard_eq_toFinset_card _ hv] at hN
    exact hN
  obtain ⟨C, hc, hbound⟩ := HDP.covering_polytopes V ε hε (by simpa [hVP] using hdiam)
  exact ⟨C, by simpa [hVP] using hc, by simpa [hcard] using hbound⟩

/-- Exercise 0.0.6, with one fixed absolute constant e and actual vertex count. -/
theorem exercise_0_0_6 {n N : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP : ∃ V : Finset (EuclideanSpace ℝ (Fin n)), P = convexHull ℝ (V : Set _))
    (hN : (P.extremePoints ℝ).ncard = N)
    (hdiam : ∀ s ∈ P, ∀ t ∈ P, ‖s - t‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin n)), HDP.BallCover P ε C ∧
      (C.card : ℝ) ≤ (Real.exp 1 + Real.exp 1 * ε ^ 2 * N) ^ ⌈1 / ε ^ 2⌉₊ := by
  classical
  obtain ⟨hv, hh⟩ := HDP.polytope_vertices hP
  let V := hv.toFinset
  have hV : (V : Set (EuclideanSpace ℝ (Fin n))) = P.extremePoints ℝ := hv.coe_toFinset
  have hVP : convexHull ℝ (V : Set _) = P := by rw [hV, hh]
  have hcard : V.card = N := by
    rw [Set.ncard_eq_toFinset_card _ hv] at hN
    exact hN
  obtain ⟨C, hc, _, hbound⟩ := HDP.improved_covering V ε hε (by simpa [hVP] using hdiam)
  exact ⟨C, by simpa [hVP] using hc, by simpa [hcard] using hbound⟩

end HDP.Source
