/-
Sharpness of Carathéodory's bound `n+1`: the barycenter of the standard
`(n+1)`-vertex simplexFinset is not in the convex hull of any proper subset of its
vertices.  This formalizes the remark following Theorem 0.0.1.
-/
import Mathlib
import HDP.Defs

open Set BigOperators
open scoped RealInnerProductSpace InnerProductSpace
set_option maxHeartbeats 1000000

namespace HDP
abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def simplexFinset (n : ℕ) : Finset (Euclid n) :=
  insert 0 (Finset.univ.image (fun i : Fin n => EuclideanSpace.single i (1:ℝ)))

lemma simplexFinset_card (n : ℕ) : (simplexFinset n).card = n + 1 := by
  have hinj : Function.Injective (fun i : Fin n => EuclideanSpace.single i (1:ℝ)) := by
    intro i j hij
    have h := congr_arg (fun x : Euclid n => x i) hij
    simp [EuclideanSpace.single_apply] at h
    by_contra hne
    simp [hne] at h
  have h0 : (0 : Euclid n) ∉ Finset.univ.image (fun i : Fin n => EuclideanSpace.single i (1:ℝ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩
    have := congr_arg (fun x : Euclid n => x i) hi.symm
    simp [EuclideanSpace.single_apply] at this
  rw [simplexFinset, Finset.card_insert_of_notMem h0, Finset.card_image_of_injective _ hinj]
  simp

noncomputable def simplexBarycenter (n : ℕ) : Euclid n :=
  (1 / ((n:ℝ) + 1)) • ∑ i : Fin n, EuclideanSpace.single i (1:ℝ)

lemma simplexBarycenter_mem (n : ℕ) : simplexBarycenter n ∈ convexHull ℝ (simplexFinset n : Set (Euclid n)) := by
  let z : Option (Fin n) → Euclid n := fun o => o.elim 0 (fun i => EuclideanSpace.single i (1:ℝ))
  apply mem_convexHull_of_exists_fintype (w := fun _ => 1 / ((n:ℝ) + 1)) (z := z)
  · intro o; positivity
  · simp [Finset.sum_const, Fintype.card_option, Fintype.card_fin]
    field_simp
  · intro o
    cases o with
    | none => simp [z, simplexFinset]
    | some i => simp [z, simplexFinset]
  · simp [z, simplexBarycenter, Finset.smul_sum]

lemma simplexBarycenter_coord (n : ℕ) (j : Fin n) : simplexBarycenter n j = 1 / ((n:ℝ) + 1) := by
  simp [simplexBarycenter]

lemma coord_eq_zero_of_mem_simplex_of_ne {n : ℕ} {z : Euclid n} (hz : z ∈ simplexFinset n)
    {j : Fin n} (hne : z ≠ EuclideanSpace.single j (1:ℝ)) : z j = 0 := by
  rw [simplexFinset, Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨k, hk, rfl⟩
  · simp
  · have hkj : k ≠ j := by
      intro h
      apply hne
      simp [h]
    simp [EuclideanSpace.single_apply, Ne.symm hkj]

lemma simplexBarycenter_sum_coord (n : ℕ) : ∑ j : Fin n, simplexBarycenter n j = (n:ℝ) / ((n:ℝ) + 1) := by
  simp [simplexBarycenter]
  field_simp


theorem caratheodory_bound_sharp (n : ℕ) :
    ∃ T : Finset (Euclid n), T.card = n + 1 ∧
      ∃ x ∈ convexHull ℝ (T : Set (Euclid n)),
        ∀ s : Finset (Euclid n), (s : Set (Euclid n)) ⊆ (T : Set (Euclid n)) →
          x ∈ convexHull ℝ (s : Set (Euclid n)) → s.card = n + 1 := by
  refine ⟨simplexFinset n, simplexFinset_card n, simplexBarycenter n, simplexBarycenter_mem n, ?_⟩
  intro s hs hx
  have hsub : simplexFinset n ⊆ s := by
    intro z hz
    rw [simplexFinset, Finset.mem_insert, Finset.mem_image] at hz
    rcases hz with rfl | ⟨j, hjk, rfl⟩
    · by_contra h0
      rw [mem_convexHull_iff_exists_fintype] at hx
      obtain ⟨ι, hι, lam, w, hlam0, hlam1, hwS, hxsum⟩ := hx
      letI : Fintype ι := hι
      have hcoord_all : ∀ j, simplexBarycenter n j = ∑ i, lam i * (w i j) := by
        intro j
        rw [← hxsum]
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hsumcoord : ∑ j : Fin n, simplexBarycenter n j = ∑ i, lam i := by
        calc
          ∑ j : Fin n, simplexBarycenter n j = ∑ j : Fin n, ∑ i, lam i * (w i j) := by
            simp_rw [hcoord_all]
          _ = ∑ i, ∑ j : Fin n, lam i * (w i j) := Finset.sum_comm
          _ = ∑ i, lam i * ∑ j : Fin n, w i j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          _ = ∑ i, lam i * 1 := by
            apply Finset.sum_congr rfl
            intro i hi
            have hwne : w i ≠ 0 := by
              intro h
              exact h0 (h ▸ hwS i)
            have hmem : w i ∈ Finset.univ.image
                (fun k : Fin n => EuclideanSpace.single k (1:ℝ)) := by
              have hz : w i ∈ simplexFinset n := hs (hwS i)
              rw [simplexFinset, Finset.mem_insert] at hz
              rcases hz with h | h
              · exact absurd h hwne
              · exact h
            rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
            rw [← hk]
            simp [EuclideanSpace.single_apply]
          _ = ∑ i, lam i := by simp
      have hbary := simplexBarycenter_sum_coord n
      rw [hbary] at hsumcoord
      have hne : (n:ℝ) / ((n:ℝ) + 1) ≠ 1 := by
        intro h
        have hden : ((n:ℝ) + 1) ≠ 0 := by positivity
        field_simp [hden] at h
        linarith
      exact hne (hsumcoord.trans hlam1)
    · by_contra hej
      rw [mem_convexHull_iff_exists_fintype] at hx
      obtain ⟨ι, hι, lam, w, hlam0, hlam1, hwS, hxsum⟩ := hx
      letI : Fintype ι := hι
      have hcoord : simplexBarycenter n j = ∑ i, lam i * (w i j) := by
        rw [← hxsum]
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hzero : ∀ i, w i j = 0 := by
        intro i
        exact coord_eq_zero_of_mem_simplex_of_ne (n := n) (hs (hwS i))
          (by intro h; exact hej (h ▸ hwS i))
      have hzero' : simplexBarycenter n j = 0 := by
        rw [hcoord]
        simp [hzero]
      have hb := simplexBarycenter_coord n j
      rw [hb] at hzero'
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  have hseq : s = simplexFinset n := Finset.Subset.antisymm (Finset.coe_subset.mp hs) hsub
  rw [hseq, simplexFinset_card]