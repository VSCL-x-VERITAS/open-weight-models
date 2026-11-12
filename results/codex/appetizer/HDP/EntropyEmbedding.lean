import HDP.Crosspolytope
import HDP.Covering

open scoped BigOperators

namespace HDP

/-- Separation forces distinct covering centers, even when centers lie outside the set. -/
theorem packing_card_le_cover_card {E α : Type*} [PseudoMetricSpace E]
    (P : Set E) (ε : ℝ) (S : Finset α) (f : α → E) (C : Finset E)
    (hmem : ∀ a ∈ S, f a ∈ P)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * ε < dist (f a) (f b))
    (hcover : ∀ x ∈ P, ∃ c ∈ C, dist x c ≤ ε) : S.card ≤ C.card := by
  classical
  choose g hgC hg using fun a : ↥S => hcover (f a) (hmem a a.property)
  apply Finset.card_le_card_of_injective (f := fun a : ↥S => (⟨g a, hgC a⟩ : ↥C))
  intro a b hab
  apply Subtype.ext
  by_contra hn
  have he : g a = g b := congrArg Subtype.val hab
  have hh := dist_triangle (f a) (g a) (f b)
  have hb := hg b
  rw [← he, dist_comm] at hb
  have hs := hsep a a.property b b.property hn
  linarith [hg a]

namespace Crosspolytope

/-- Extend finite coordinates by zero along an injection. -/
noncomputable def coordinateEmbedding {ι : Type*} {n : ℕ}
    (e : ι ↪ Fin n) (x : ι → ℝ) : Space n :=
  WithLp.toLp 2 (Function.extend e x (fun _ => 0))

@[simp] theorem coordinateEmbedding_apply {ι : Type*} {n : ℕ}
    (e : ι ↪ Fin n) (x : ι → ℝ) (i : ι) :
    coordinateEmbedding e x (e i) = x i := by
  exact e.injective.extend_apply x (fun _ => 0) i

@[simp] theorem coordinateEmbedding_apply_of_not_range {ι : Type*} {n : ℕ}
    (e : ι ↪ Fin n) (x : ι → ℝ) {j : Fin n} (hj : j ∉ Set.range e) :
    coordinateEmbedding e x j = 0 := by
  exact Function.extend_apply' x (fun _ => 0) j hj

theorem coordinateEmbedding_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ↪ Fin n) (x : ι → ℝ) (g : ℝ → ℝ) (hg : g 0 = 0) :
    ∑ j, g (coordinateEmbedding e x j) = ∑ i, g (x i) := by
  classical
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    rw [coordinateEmbedding_apply_of_not_range e x hj, hg]
  · intro i
    rw [coordinateEmbedding_apply]

theorem l1Norm_coordinateEmbedding {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ↪ Fin n) (x : ι → ℝ) :
    l1Norm (coordinateEmbedding e x) = ∑ i, |x i| := by
  exact coordinateEmbedding_sum e x abs (abs_zero)

theorem dist_sq_coordinateEmbedding {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ↪ Fin n) (x y : ι → ℝ) :
    dist (coordinateEmbedding e x) (coordinateEmbedding e y) ^ 2 =
      ∑ i, (x i - y i)^2 := by
  classical
  rw [EuclideanSpace.dist_sq_eq]
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    simp [coordinateEmbedding_apply_of_not_range e _ hj]
  · intro i
    simp [Real.dist_eq, sq_abs]

/-- One occupied coordinate in each block, scaled to have l1 norm one half. -/
noncomputable def sparseWord {d q n : ℕ} (e : (Fin d × Fin q) ↪ Fin n)
    (w : Fin d → Fin q) : Space n :=
  coordinateEmbedding e (fun p => if p.2 = w p.1 then 1 / (2 * (d : ℝ)) else 0)

theorem sparseWord_mem_body {d q n : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (e : (Fin d × Fin q) ↪ Fin n) (w : Fin d → Fin q) :
    sparseWord e w ∈ body n := by
  apply mem_body_of_l1Norm_le_half hn
  rw [sparseWord, l1Norm_coordinateEmbedding]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 ≤ 1 / (2 * (d : ℝ)) := by positivity
  simp only [Fintype.sum_prod_type]
  simp_rw [apply_ite abs, abs_of_nonneg ha, abs_zero]
  simp
  field_simp
  norm_num

private theorem onehot_diff_sq {q : ℕ} (a : ℝ) (u v : Fin q) :
    (∑ j : Fin q, ((if j = u then a else 0) - (if j = v then a else 0))^2) =
      if u = v then 0 else 2 * a^2 := by
  classical
  by_cases h : u = v
  · simp [h]
  · have he (j : Fin q) :
        ((if j = u then a else 0) - (if j = v then a else 0))^2 =
          (if j = u then a^2 else 0) + (if j = v then a^2 else 0) := by
      by_cases hu : j = u <;> by_cases hv : j = v <;> simp_all
    simp_rw [he]
    simp [Finset.sum_add_distrib, h, two_mul]

theorem sparseWord_dist_sq {d q n : ℕ} (_hd : 1 ≤ d)
    (e : (Fin d × Fin q) ↪ Fin n) (u v : Fin d → Fin q) :
    dist (sparseWord e u) (sparseWord e v)^2 =
      (hammingDist u v : ℝ) / (2 * (d : ℝ)^2) := by
  classical
  rw [sparseWord, sparseWord, dist_sq_coordinateEmbedding]
  simp only [Fintype.sum_prod_type]
  simp_rw [onehot_diff_sq]
  have hh : (∑ i : Fin d, if u i = v i then (0 : ℝ) else 2 * (1 / (2 * (d : ℝ)))^2) =
      (hammingDist u v : ℝ) * (2 * (1 / (2 * (d : ℝ)))^2) := by
    simp [hammingDist, Finset.sum_ite]
  rw [hh]
  ring

/-- Integer grid in selected coordinates, scaled inside the half l1 ball. -/
noncomputable def denseWord {d q n : ℕ} (e : Fin d ↪ Fin n)
    (w : Fin d → Fin q) : Space n :=
  coordinateEmbedding e (fun i => (w i : ℝ) / (2 * (d : ℝ) * q))

theorem denseWord_mem_body {d q n : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 1 ≤ q)
    (e : Fin d ↪ Fin n) (w : Fin d → Fin q) :
    denseWord e w ∈ body n := by
  apply mem_body_of_l1Norm_le_half hn
  rw [denseWord, l1Norm_coordinateEmbedding]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ ∑ _i : Fin d, (q : ℝ) / (2 * (d : ℝ) * q) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (w i).isLt.le
    _ = 1/2 := by simp; field_simp

private theorem one_le_sq_fin_sub {q : ℕ} {u v : Fin q} (h : u ≠ v) :
    (1 : ℝ) ≤ ((u : ℝ) - (v : ℝ))^2 := by
  have hval : u.val ≠ v.val := fun hh => h (Fin.ext hh)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hh : (u : ℝ) + 1 ≤ v := by exact_mod_cast hlt
    nlinarith
  · have hh : (v : ℝ) + 1 ≤ u := by exact_mod_cast hgt
    nlinarith

theorem denseWord_hamming_le_dist_sq {d q n : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (e : Fin d ↪ Fin n) (u v : Fin d → Fin q) :
    (hammingDist u v : ℝ) ≤
      (2 * (d : ℝ) * q)^2 * dist (denseWord e u) (denseWord e v)^2 := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [denseWord, denseWord, dist_sq_coordinateEmbedding]
  have hden : 2 * (d : ℝ) * q ≠ 0 := by positivity
  have he (i : Fin d) :
      (2 * (d : ℝ) * q)^2 *
        ((u i : ℝ) / (2 * (d : ℝ) * q) - (v i : ℝ) / (2 * (d : ℝ) * q))^2 =
        ((u i : ℝ) - (v i : ℝ))^2 := by field_simp
  rw [Finset.mul_sum]
  simp_rw [he]
  rw [hammingDist]
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => u i ≠ v i), (1 : ℝ) := by simp
    _ ≤ ∑ i : Fin d, if u i ≠ v i then ((u i : ℝ) - (v i : ℝ))^2 else 0 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      exact one_le_sq_fin_sub (Finset.mem_filter.mp hi).2
    _ ≤ _ := Finset.sum_le_sum fun i _ => by split_ifs <;> nlinarith [sq_nonneg ((u i : ℝ) - (v i : ℝ))]

/-- Sparse block code separation transfers to every ambient ball cover. -/
theorem sparse_code_card_le_cover_card {m q n : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (hdim : (2*m)*q ≤ n) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : 16 * ε^2 * (2 * (m : ℝ)) < 1)
    (A : Finset (Fin (2*m) → Fin q))
    (hsep : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → m < hammingDist u v)
    (C : Finset (Space n)) (hcover : BallCover (body n) ε C) :
    A.card ≤ C.card := by
  classical
  let e : (Fin (2*m) × Fin q) ↪ Fin n := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa using hdim))
  have hn : 1 ≤ n := by nlinarith
  have hd : 1 ≤ 2*m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply packing_card_le_cover_card (body n) ε A (sparseWord e) C
  · intro u _
    exact sparseWord_mem_body hn hd e u
  · intro u hu v hv huv
    have hh : (m : ℝ) < hammingDist u v := by exact_mod_cast hsep u hu v hv huv
    have hdist := sparseWord_dist_sq hd e u v
    push_cast at hdist
    have hden : 0 < 2 * (2 * (m : ℝ))^2 := by positivity
    have hprod : dist (sparseWord e u) (sparseWord e v)^2 *
        (2 * (2 * (m : ℝ))^2) = (hammingDist u v : ℝ) :=
      (eq_div_iff (ne_of_gt hden)).mp hdist
    have hsq : 4 * ε^2 < dist (sparseWord e u) (sparseWord e v)^2 := by
      nlinarith
    nlinarith [show 0 ≤ dist (sparseWord e u) (sparseWord e v) from dist_nonneg]
  · simpa [BallCover, Metric.mem_closedBall] using hcover

/-- A 64-letter grid code separated in half its coordinates defeats small covers. -/
theorem dense_code_card_le_cover_card {k n : ℕ} (hk : 1 ≤ k) (hdim : k ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : 32 * ε^2 * (k : ℝ) * 64^2 < 1)
    (A : Finset (Fin k → Fin 64))
    (hsep : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → k/2 < hammingDist u v)
    (C : Finset (Space n)) (hcover : BallCover (body n) ε C) :
    A.card ≤ C.card := by
  classical
  let e : Fin k ↪ Fin n := Fin.castLEEmb hdim
  have hn : 1 ≤ n := hk.trans hdim
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply packing_card_le_cover_card (body n) ε A (denseWord e) C
  · intro u _
    exact denseWord_mem_body hn hk (by norm_num) e u
  · intro u hu v hv huv
    have hhN := hsep u hu v hv huv
    have hhN' : k < 2 * hammingDist u v := by omega
    have hh : (k : ℝ) < 2 * (hammingDist u v : ℝ) := by exact_mod_cast hhN'
    have hdist := denseWord_hamming_le_dist_sq hk (by norm_num : 1 ≤ 64) e u v
    norm_num at hdist
    have hsq : 4 * ε^2 < dist (denseWord e u) (denseWord e v)^2 := by
      nlinarith
    nlinarith [show 0 ≤ dist (denseWord e u) (denseWord e v) from dist_nonneg]
  · simpa [BallCover, Metric.mem_closedBall] using hcover

end Crosspolytope
end HDP
