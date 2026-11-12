import Mathlib

open scoped BigOperators
namespace HDP

/-- A maximal finite separated family covers the finite universe by its relation balls. -/
theorem exists_finite_relation_packing {α : Type*} [Fintype α]
    (R : α → α → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ x y, R x y → R y x) :
    ∃ C : Finset α,
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ R x y) ∧
      (∀ y, ∃ x ∈ C, R x y) := by
  classical
  let good : Finset (Finset α) := Finset.univ.filter
    (fun C => ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ R x y)
  have hempty : ∅ ∈ good := by simp [good]
  obtain ⟨C, hC, hmax⟩ := good.exists_max_image Finset.card ⟨∅, hempty⟩
  have hsep := (Finset.mem_filter.mp hC).2
  refine ⟨C, hsep, ?_⟩
  intro y
  by_contra hn
  push_neg at hn
  have hy : y ∉ C := fun hy => hn y hy (hrefl y)
  have hins : insert y C ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha b hb hab
    by_cases hay : a = y
    · subst a
      have hby : b ≠ y := Ne.symm hab
      have hbC : b ∈ C := (Finset.mem_insert.mp hb).resolve_left hby
      exact fun h => hn b hbC (hsymm _ _ h)
    · have haC : a ∈ C := (Finset.mem_insert.mp ha).resolve_left hay
      by_cases hby : b = y
      · subst b
        exact hn a haC
      · exact hsep a haC b ((Finset.mem_insert.mp hb).resolve_left hby) hab
  have hh := hmax _ hins
  rw [Finset.card_insert_of_notMem hy] at hh
  omega

/-- The finite greedy bound for symmetric relation balls of uniformly bounded size. -/
theorem exists_finite_relation_packing_card {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R] (hrefl : ∀ x, R x x)
    (hsymm : ∀ x y, R x y → R y x) (B : ℕ)
    (hball : ∀ x, (Finset.univ.filter (R x)).card ≤ B) :
    ∃ C : Finset α,
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ¬ R x y) ∧
      Fintype.card α ≤ C.card * B := by
  classical
  obtain ⟨C, hsep, hcover⟩ := exists_finite_relation_packing R hrefl hsymm
  refine ⟨C, hsep, ?_⟩
  have hsub : Finset.univ ⊆ C.biUnion (fun x => Finset.univ.filter (R x)) := by
    intro y _
    obtain ⟨x, hx, hxy⟩ := hcover y
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩
  calc
    Fintype.card α = (Finset.univ : Finset α).card := by simp
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ C, (Finset.univ.filter (R x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ C, B := Finset.sum_le_sum fun x _ => hball x
    _ = C.card * B := by simp

/-- Words agreeing with a fixed word off `S` have at most `q ^ |S|` possibilities. -/
lemma hamming_cylinder_card_le (d q : ℕ) (x : Fin d → Fin q)
    (S : Finset (Fin d)) :
    (Finset.univ.filter (fun y : Fin d → Fin q => ∀ i, i ∉ S → y i = x i)).card ≤
      q ^ S.card := by
  classical
  let A := Finset.univ.filter (fun y : Fin d → Fin q => ∀ i, i ∉ S → y i = x i)
  have hinj : Set.InjOn (fun y : Fin d → Fin q => fun i : S => y i) (A : Set _) := by
    intro y hy z hz heq
    have hy' := (Finset.mem_filter.mp hy).2
    have hz' := (Finset.mem_filter.mp hz).2
    funext i
    by_cases hi : i ∈ S
    · exact congrFun heq ⟨i, hi⟩
    · exact (hy' i hi).trans (hz' i hi).symm
  calc
    A.card ≤ (Finset.univ : Finset (S → Fin q)).card :=
      Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    _ = q ^ S.card := by simp

/-- A deliberately coarse Hamming-ball estimate sufficient for absolute entropy constants. -/
theorem hamming_ball_card_le (d q r : ℕ) (hq : 1 ≤ q) (x : Fin d → Fin q) :
    (Finset.univ.filter (fun y : Fin d → Fin q => hammingDist x y ≤ r)).card ≤
      2 ^ d * q ^ r := by
  classical
  let sets := (Finset.univ : Finset (Fin d)).powerset.filter (fun S => S.card ≤ r)
  let cyl := fun S : Finset (Fin d) =>
    Finset.univ.filter (fun y : Fin d → Fin q => ∀ i, i ∉ S → y i = x i)
  have hsub : (Finset.univ.filter (fun y : Fin d → Fin q => hammingDist x y ≤ r)) ⊆
      sets.biUnion cyl := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    let S := Finset.univ.filter (fun i => x i ≠ y i)
    apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), hy'⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i hi
      have : ¬ x i ≠ y i := by simpa [S] using hi
      exact (not_not.mp this).symm
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ S ∈ sets, (cyl S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ sets, q ^ r := by
      apply Finset.sum_le_sum
      intro S hS
      exact (hamming_cylinder_card_le d q x S).trans
        (Nat.pow_le_pow_right hq (Finset.mem_filter.mp hS).2)
    _ = sets.card * q ^ r := by simp
    _ ≤ 2 ^ d * q ^ r := by
      gcongr
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-- Finite Gilbert greedy packing, with no assumed packing hypothesis. -/
theorem exists_hamming_code (d q r : ℕ) (hq : 1 ≤ q) :
    ∃ C : Finset (Fin d → Fin q),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → r < hammingDist x y) ∧
      q ^ d ≤ C.card * (2 ^ d * q ^ r) := by
  classical
  obtain ⟨C, hsep, hcard⟩ := exists_finite_relation_packing_card
    (fun x y : Fin d → Fin q => hammingDist x y ≤ r)
    (fun x => by simp) (fun x y h => by simpa [hammingDist_comm] using h)
    (2 ^ d * q ^ r) (hamming_ball_card_le d q r hq)
  refine ⟨C, ?_, ?_⟩
  · intro x hx y hy hxy
    exact Nat.lt_of_not_ge (hsep x hx y hy hxy)
  · simpa using hcard

/-- Cancellation form of the greedy estimate, convenient for taking logarithms. -/
theorem exists_hamming_code_reduced (d q r : ℕ) (hq : 1 ≤ q) (hr : r ≤ d) :
    ∃ C : Finset (Fin d → Fin q),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → r < hammingDist x y) ∧
      q ^ (d-r) ≤ C.card * 2 ^ d := by
  obtain ⟨C, hsep, hcard⟩ := exists_hamming_code d q r hq
  refine ⟨C, hsep, ?_⟩
  have hqpos : 0 < q ^ r := pow_pos (by omega : 0 < q) _
  apply Nat.le_of_mul_le_mul_right ?_ hqpos
  calc
    q ^ (d-r) * q ^ r = q ^ d := by rw [← pow_add, Nat.sub_add_cancel hr]
    _ ≤ C.card * (2 ^ d * q ^ r) := hcard
    _ = C.card * 2 ^ d * q ^ r := by ring

/-- Turn a strict numerical rate estimate into a strict code-cardinality bound. -/
theorem exists_hamming_code_card_gt (d q r k : ℕ) (hq : 1 ≤ q) (hr : r ≤ d)
    (hrate : 2 ^ (k-1+d) < q ^ (d-r)) :
    ∃ C : Finset (Fin d → Fin q),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → r < hammingDist x y) ∧
      2 ^ (k-1) < C.card := by
  obtain ⟨C, hsep, hcard⟩ := exists_hamming_code_reduced d q r hq hr
  refine ⟨C, hsep, ?_⟩
  apply Nat.lt_of_mul_lt_mul_right
  calc
    2 ^ (k-1) * 2 ^ d = 2 ^ (k-1+d) := by rw [pow_add]
    _ < q ^ (d-r) := hrate
    _ ≤ C.card * 2 ^ d := hcard

/-- A fixed 64-letter alphabet already supplies exponentially many words at half distance. -/
theorem exists_dense_hamming_code (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : Finset (Fin k → Fin 64),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → k/2 < hammingDist x y) ∧
      2 ^ (k-1) < C.card := by
  apply exists_hamming_code_card_gt k 64 (k/2) k (by omega) (Nat.div_le_self _ _)
  have hexp : k-1+k < 6*(k-k/2) := by omega
  calc
    2 ^ (k-1+k) < 2 ^ (6*(k-k/2)) := Nat.pow_lt_pow_right (by omega) hexp
    _ = 64 ^ (k-k/2) := by rw [pow_mul]; norm_num

/-- Even-length specialization used by sparse block codes. -/
theorem exists_sparse_hamming_code (m q k : ℕ) (hq : 1 ≤ q)
    (hrate : 2 ^ (k-1+2*m) < q ^ m) :
    ∃ C : Finset (Fin (2*m) → Fin q),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → m < hammingDist x y) ∧
      2 ^ (k-1) < C.card := by
  apply exists_hamming_code_card_gt (2*m) q m k hq (by omega)
  have hm : 2*m-m = m := by omega
  simpa [hm] using hrate

end HDP
