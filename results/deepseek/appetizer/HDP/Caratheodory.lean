/-
Carathéodory's theorem, Theorem 0.0.1 of the source.
-/
import Mathlib
import HDP.Defs

open Set BigOperators

namespace HDP

/-- Theorem 0.0.1: every point of the convex hull of `T ⊆ ℝⁿ` is a convex
combination of at most `n + 1` points of `T`. -/
theorem caratheodory {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ T) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin n)), (↑s : Set _) ⊆ T ∧
      x ∈ convexHull ℝ (↑s) ∧ s.card ≤ n + 1 := by
  let s := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨s, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx, ?_⟩
  have hcard :=
    (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
  have hfr : Module.finrank ℝ
      (vectorSpan ℝ (Set.range ((↑) : s → EuclideanSpace ℝ (Fin n)))) ≤ n := by
    calc
      _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.finrank_le _
      _ = n := finrank_euclideanSpace_fin
  calc
    s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ Module.finrank ℝ (vectorSpan ℝ
        (Set.range ((↑) : s → EuclideanSpace ℝ (Fin n)))) + 1 := hcard
    _ ≤ n + 1 := by omega

end HDP
