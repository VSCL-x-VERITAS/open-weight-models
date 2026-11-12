/-
Binomial coefficient estimates used in Exercise 0.0.5 and Exercise 0.0.6.
-/
import Mathlib

open Set BigOperators
open scoped Real

namespace HDP

/-- `(k/e)^k ≤ k!`, the lower Stirling bound used for the single-term estimate. -/
lemma factorial_ge_div_exp_pow (k : ℕ) (hk : 0 < k) :
    ((k:ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have hst := Stirling.le_factorial_stirling k
  have hsqrt : (1:ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    rw [Real.one_le_sqrt]
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.pi_gt_three, hk1]
  have hnonneg : (0:ℝ) ≤ ((k:ℝ) / Real.exp 1) ^ k := by positivity
  calc
    ((k:ℝ) / Real.exp 1) ^ k
        ≤ Real.sqrt (2 * Real.pi * k) * ((k:ℝ) / Real.exp 1) ^ k := by
          nlinarith [hsqrt, hnonneg]
    _ ≤ (k.factorial : ℝ) := hst

/-- `C(n,k) ≤ (e n / k)^k` for `k > 0`. -/
lemma choose_le_exp_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
  have hfact := factorial_ge_div_exp_pow k hk
  have hfactpos : (0:ℝ) < ((k:ℝ) / Real.exp 1) ^ k := by positivity
  have hchoose : (n.choose k : ℝ) ≤ (n:ℝ) ^ k / (k.factorial : ℝ) := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) k n)
  calc
    (n.choose k : ℝ) ≤ (n:ℝ) ^ k / (k.factorial : ℝ) := hchoose
    _ ≤ (n:ℝ) ^ k / (((k:ℝ) / Real.exp 1) ^ k) := by gcongr
    _ = (Real.exp 1 * n / k) ^ k := by
      rw [div_pow, div_pow, mul_pow]
      field_simp

/-- The product formula `C(n,m) = ∏_{i<m} (n-i)/(m-i)` for `m ≤ n`. -/
lemma prod_range_sub_eq_factorial (m : ℕ) :
    (∏ i ∈ Finset.range m, ((m - i : ℕ) : ℝ)) = (m.factorial : ℝ) := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast
  conv_rhs => rw [← Finset.prod_range_reflect (fun i => ((i : ℝ) + 1)) m]
  apply Finset.prod_congr rfl
  intro i hi
  have hi' : i < m := Finset.mem_range.mp hi
  have h : m - i = (m - 1 - i) + 1 := by omega
  rw [h]
  push_cast
  ring

lemma choose_eq_prod_range (n m : ℕ) (_hm : m ≤ n) :
    (n.choose m : ℝ) =
      ∏ i ∈ Finset.range m, (((n - i : ℕ) : ℝ) / ((m - i : ℕ) : ℝ)) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial n m)
    (by exact_mod_cast Nat.factorial_ne_zero m)]
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← prod_range_sub_eq_factorial m]
  rw [Finset.prod_div_distrib]

/-- Lower bound of Exercise 0.0.5: `(n/m)^m ≤ C(n,m)`. -/
lemma choose_ge_pow_div (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ((n:ℝ) / (m:ℝ)) ^ m ≤ (n.choose m : ℝ) := by
  rw [choose_eq_prod_range n m hmn]
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  calc
    ((n:ℝ) / (m:ℝ)) ^ m = ∏ i ∈ Finset.range m, ((n:ℝ) / (m:ℝ)) := by
      rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range m, (((n - i : ℕ) : ℝ) / ((m - i : ℕ) : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hi' : i < m := Finset.mem_range.mp hi
        have hmi : (0:ℝ) < ((m - i : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_pos_of_lt hi'
        rw [div_le_div_iff₀ hmpos hmi]
        have hni_cast : ((n - i : ℕ) : ℝ) = (n:ℝ) - i := by
          rw [Nat.cast_sub (by omega : i ≤ n)]
        have hmi_cast : ((m - i : ℕ) : ℝ) = (m:ℝ) - i := by
          rw [Nat.cast_sub (by omega : i ≤ m)]
        rw [hni_cast, hmi_cast]
        have hiR : (0:ℝ) ≤ (i:ℝ) := by positivity
        have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
        have hle : (i:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_trans hi'.le hmn
        have him : (i:ℝ) < (m:ℝ) := by exact_mod_cast hi'
        have hmnR : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
        nlinarith

/-- Upper bound of Exercise 0.0.5: `∑_{k=0}^m C(n,k) ≤ (e n/m)^m`. -/
lemma sum_choose_le_exp (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤
      (Real.exp 1 * n / m) ^ m := by
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hnpos : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hm1) hmn
  let x : ℝ := (m:ℝ) / (n:ℝ)
  have hxpos : 0 < x := by positivity
  have hx0 : 0 ≤ x := le_of_lt hxpos
  have hx1 : x ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast hmn
  let S : ℝ := ∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)
  have hstep1 : x ^ m * S ≤ ∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * x ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : x ^ m ≤ x ^ k := pow_le_pow_of_le_one hx0 hx1 hkm
    calc
      x ^ m * (n.choose k : ℝ) ≤ x ^ k * (n.choose k : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ = (n.choose k : ℝ) * x ^ k := by ring
  have hstep2 : (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * x ^ k)
      ≤ (x + 1) ^ n := by
    have hsum_le : (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * x ^ k)
        ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · rw [Finset.range_subset_range]
        omega
      · intro k hk hknot
        positivity
    calc
      (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * x ^ k)
          ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * x ^ k := hsum_le
      _ = (x + 1) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        simp [mul_comm]
  have hstep3 : (x + 1) ^ n ≤ Real.exp (m:ℝ) := by
    have hle : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have hpow : (x + 1) ^ n ≤ (Real.exp x) ^ n :=
      pow_le_pow_left₀ (by positivity : 0 ≤ x + 1) hle n
    calc
      (x + 1) ^ n ≤ (Real.exp x) ^ n := hpow
      _ = Real.exp ((n:ℝ) * x) := (Real.exp_nat_mul x n).symm
      _ = Real.exp (m:ℝ) := by
        congr 1
        dsimp [x]
        field_simp
  have hmain : S ≤ Real.exp (m:ℝ) / x ^ m := by
    rw [le_div_iff₀ (pow_pos hxpos m)]
    calc
      S * x ^ m = x ^ m * S := by ring
      _ ≤ ∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ) * x ^ k := hstep1
      _ ≤ (x + 1) ^ n := hstep2
      _ ≤ Real.exp (m:ℝ) := hstep3
  calc
    S ≤ Real.exp (m:ℝ) / x ^ m := hmain
    _ = (Real.exp 1 * n / m) ^ m := by
      dsimp [S, x]
      rw [show Real.exp (m:ℝ) = (Real.exp 1) ^ m by
        simp]
      rw [div_pow, div_pow, mul_pow]
      field_simp

/-- Exercise 0.0.5: all three binomial inequalities. -/
theorem sum_choose_bounds (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ((n:ℝ) / (m:ℝ)) ^ m ≤ (n.choose m : ℝ) ∧
      (n.choose m : ℝ) ≤ (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ∧
      (∑ k ∈ Finset.range (m + 1), (n.choose k : ℝ)) ≤
        (Real.exp 1 * n / m) ^ m := by
  refine ⟨choose_ge_pow_div n m hm1 hmn, ?_, sum_choose_le_exp n m hm1 hmn⟩
  exact Finset.single_le_sum (s := Finset.range (m + 1)) (a := m)
    (f := fun k => (n.choose k : ℝ))
    (fun k hk => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m))

end HDP
