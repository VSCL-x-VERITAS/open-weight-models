/-
Exercise 0.0.6: the improved covering bound for polytopes, using the
number of multisets of vertices and the single binomial estimate
`C(n,k) ≤ (e n / k)^k`.
-/
import Mathlib
import HDP.Approximate
import HDP.Binomial

open Set BigOperators MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace InnerProductSpace
set_option maxHeartbeats 1000000

namespace HDP

lemma one_div_ceil_inv_sq_le_sq {ε : ℝ} (hε : 0 < ε) :
    1 / (Nat.ceil (1 / ε ^ 2) : ℝ) ≤ ε ^ 2 := by
  have hpos : (0:ℝ) < 1 / ε ^ 2 := by positivity
  have hle : 1 / ε ^ 2 ≤ (Nat.ceil (1 / ε ^ 2) : ℝ) := Nat.le_ceil _
  have h := one_div_le_one_div_of_le hpos hle
  simpa [one_div] using h

lemma choose_multichoose_bound {N k : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hk : k = Nat.ceil (1 / ε ^ 2)) :
    (Nat.choose (N + k - 1) k : ℝ) ≤ (4 + 4 * ε ^ 2 * N) ^ k := by
  let n : ℕ := N + k - 1
  have hkpos : 0 < k := by
    rw [hk]
    exact Nat.ceil_pos.mpr (by positivity)
  have hkposR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hNnonneg : (0:ℝ) ≤ (N:ℝ) := by positivity
  have h1k : 1 / (k:ℝ) ≤ ε ^ 2 := by
    rw [hk]
    exact one_div_ceil_inv_sq_le_sq hε
  have he4 : Real.exp 1 ≤ 4 :=
    le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
  have hbase_nonneg : (0:ℝ) ≤ 4 + 4 * ε ^ 2 * (N:ℝ) := by
    nlinarith [hNnonneg, sq_nonneg ε]
  have hbase : Real.exp 1 * (n:ℝ) / k ≤ 4 + 4 * ε ^ 2 * N := by
    have hstep1 : Real.exp 1 * (n:ℝ) / k ≤ Real.exp 1 * ((N:ℝ) / k + 1) := by
      have hle : (n:ℝ) ≤ (N:ℝ) + k := by
        dsimp [n]
        exact_mod_cast Nat.sub_le (N + k) 1
      have hdiv : (n:ℝ) / k ≤ ((N:ℝ) + k) / k := by gcongr
      have hsplit : ((N:ℝ) + k) / k = (N:ℝ) / k + 1 := by
        field_simp
      rw [hsplit] at hdiv
      calc
        Real.exp 1 * (n:ℝ) / k = Real.exp 1 * ((n:ℝ) / k) := by ring
        _ ≤ Real.exp 1 * ((N:ℝ) / k + 1) := by gcongr
    have hstep2 : Real.exp 1 * ((N:ℝ) / k + 1) ≤ 4 + 4 * ε ^ 2 * N := by
      have hNk : Real.exp 1 * ((N:ℝ) / k) ≤ 4 * ((N:ℝ) * ε ^ 2) := by
        rw [div_eq_mul_inv]
        have h1 : Real.exp 1 * ((N:ℝ) * (k:ℝ)⁻¹) ≤ 4 * ((N:ℝ) * ε ^ 2) := by
          have := mul_le_mul he4 (mul_le_mul_of_nonneg_left h1k hNnonneg)
            (by positivity) (by positivity)
          simpa [mul_assoc, mul_comm, mul_left_comm] using this
        simpa [div_eq_mul_inv] using h1
      nlinarith [he4, hNk, hNnonneg]
    calc
      Real.exp 1 * (n:ℝ) / k ≤ Real.exp 1 * ((N:ℝ) / k + 1) := hstep1
      _ ≤ 4 + 4 * ε ^ 2 * N := hstep2
  calc
    (Nat.choose (N + k - 1) k : ℝ) = (Nat.choose n k : ℝ) := by rfl
    _ ≤ (Real.exp 1 * (n:ℝ) / k) ^ k := choose_le_exp_mul_div_pow n k hkpos
    _ ≤ (4 + 4 * ε ^ 2 * N) ^ k :=
      pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp 1 * (n:ℝ) / k) hbase k


/-- Exercise 0.0.6: a polytope with `N` vertices and diameter at most `1`
is covered by at most `(4 + 4 ε² N) ^ ⌈1/ε²⌉` balls of radius `ε`. -/
theorem improved_covering {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hbdd : Bornology.IsBounded (s : Set (EuclideanSpace ℝ (Fin n))))
    (hdiam : Metric.diam (s : Set (EuclideanSpace ℝ (Fin n))) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
      C.card ≤ (4 + 4 * ε ^ 2 * s.card) ^ Nat.ceil (1 / ε ^ 2) ∧
      ∀ x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))),
        ∃ c ∈ C, dist x c ≤ ε := by
  let k := Nat.ceil (1 / ε ^ 2)
  have hk : 0 < k := Nat.ceil_pos.mpr (by positivity)
  by_cases hne : s.Nonempty
  · let centerOf : Sym s k → EuclideanSpace ℝ (Fin n) :=
      fun m => (1 / (k:ℝ)) • (m.toMultiset.map (fun v : s => (v : EuclideanSpace ℝ (Fin n)))).sum
    let C : Finset (EuclideanSpace ℝ (Fin n)) := Finset.univ.image centerOf
    refine ⟨C, ?_, ?_⟩
    · have hcardNat : C.card ≤ Nat.choose (s.card + k - 1) k := by
        calc
          C.card ≤ Fintype.card (Sym s k) := Finset.card_image_le
          _ = Nat.choose (Fintype.card s + k - 1) k := Sym.card_sym_eq_choose k
          _ = Nat.choose (s.card + k - 1) k := by simp [Fintype.card_coe]
      have hN : 0 < s.card := Finset.card_pos.mpr hne
      have hbound : (Nat.choose (s.card + k - 1) k : ℝ) ≤
          (4 + 4 * ε ^ 2 * s.card) ^ k := choose_multichoose_bound hN hε (by rfl)
      exact le_trans (by exact_mod_cast hcardNat) hbound
    · intro x hx
      obtain ⟨y, hyT, hdist⟩ := approximate_caratheodory (T := (s : Set (EuclideanSpace ℝ (Fin n))))
        (x := x) hbdd (D := 1) (by norm_num) (by simpa using hdiam) hx hk
      let y' : Fin k → s := fun j => ⟨y j, hyT j⟩
      let mult : Multiset s := Finset.univ.val.map y'
      have hcard : mult.card = k := by simp [mult]
      let m : Sym s k := Sym.mk mult hcard
      refine ⟨centerOf m, Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩, ?_⟩
      have hcenter : centerOf m = (1 / (k:ℝ)) • ∑ j, y j := by
        simp [centerOf, m, mult, y', List.sum_ofFn]
      have hle : 1 / Real.sqrt (k:ℝ) ≤ ε := inv_sqrt_ceil_le hε
      calc
        dist x (centerOf m) = ‖x - (1 / (k:ℝ)) • ∑ j, y j‖ := by
          rw [hcenter, dist_eq_norm]
        _ ≤ 1 / Real.sqrt (k:ℝ) := hdist
        _ ≤ ε := hle
  · have hempty : (s : Set (EuclideanSpace ℝ (Fin n))) = ∅ := by
      rw [← Finset.coe_empty, Finset.coe_inj]
      exact Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.card_empty]
      simp only [Nat.cast_zero]
      apply pow_nonneg
      positivity
    · intro x hx
      simp [hempty] at hx

end HDP
