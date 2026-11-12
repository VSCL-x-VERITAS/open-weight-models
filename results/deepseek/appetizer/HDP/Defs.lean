/-
Convex combinations and convex hull, following the definitions in the
Appetizer section (equation (0.1) and the displayed definition of conv(T)).
-/
import Mathlib

open Set BigOperators

namespace HDP

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]

/-- Equation (0.1): a convex combination of the points `z i` with weights `λ i`. -/
def IsConvexCombination {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → E) (x : E) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∑ i, w i • z i = x)

/-- The convex hull is the set of all finite convex combinations of points of `T`. -/
theorem mem_convexHull_iff_exists_convexCombination {T : Set E} {x : E} :
    x ∈ convexHull ℝ T ↔
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E),
        IsConvexCombination w z x ∧ ∀ i, z i ∈ T := by
  rw [mem_convexHull_iff_exists_fintype]
  constructor
  · rintro ⟨ι, hι, w, z, hw0, hw1, hz, hx⟩
    exact ⟨ι, hι, w, z, ⟨hw0, hw1, hx⟩, hz⟩
  · rintro ⟨ι, hι, w, z, ⟨hw0, hw1, hx⟩, hz⟩
    exact ⟨ι, hι, w, z, hw0, hw1, hz, hx⟩

/-- The diameter used in the source, `sup {‖s - t‖₂ : s, t ∈ T}`.
For unbounded sets the `iSup` is not the source's extended value; the main
theorems therefore use the equivalent pairwise-distance hypothesis
`DiameterLe T D`. -/
noncomputable def diameter (T : Set E) : ℝ := ⨆ p : T × T, ‖(p.1 : E) - (p.2 : E)‖

/-- `DiameterLe T D` says that all pairwise distances in `T` are at most `D`.
For nonempty `T` this is the finite-diameter form of `diameter T ≤ D`. -/
def DiameterLe (T : Set E) (D : ℝ) : Prop := ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ D

end HDP
