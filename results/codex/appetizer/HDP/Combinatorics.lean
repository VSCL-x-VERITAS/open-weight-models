import Mathlib

open scoped BigOperators
open Finset
namespace HDP

/-- The lower binomial coefficient estimate, including the zero-index case. -/
theorem pow_div_le_choose (n m : ℕ) (hmn : m ≤ n) :
    ((n : ℝ) / m) ^ m ≤ (n.choose m : ℝ) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hm : (0 : ℝ) < m + 1 := by positivity
      have hm' : (0 : ℝ) < m + 1 + 1 := by positivity
      have hmn' : m + 1 ≤ n := by omega
      have hratio : ((n : ℝ) + 1) / (m + 1 + 1) ≤ n / (m + 1) := by
        apply (div_le_div_iff₀ hm' hm).2
        have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn'
        nlinarith
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) / (m + 1 + 1)) hratio (m+1)
      have hrec : ((n + 1).choose (m + 1 + 1) : ℝ) =
          (((n : ℝ) + 1) / (m + 1 + 1)) * (n.choose (m+1) : ℝ) := by
        have h := Nat.add_one_mul_choose_eq n (m+1)
        have hc : ((n : ℝ) + 1) * (n.choose (m+1) : ℝ) =
            ((n+1).choose (m+1+1) : ℝ) * ((m : ℝ)+1+1) := by exact_mod_cast h
        field_simp
        nlinarith [hc]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
        calc
          (((n : ℝ)+1) / (m+1+1)) ^ (m+1+1) =
              (((n : ℝ)+1) / (m+1+1)) * ((((n : ℝ)+1) / (m+1+1)) ^ (m+1)) := by ring
          _ ≤ (((n : ℝ)+1) / (m+1+1)) * (n.choose (m+1) : ℝ) :=
            mul_le_mul_of_nonneg_left (hpow.trans (by simpa only [Nat.cast_add, Nat.cast_one] using ih n hmn')) (by positivity)
          _ = ((n+1).choose (m+1+1) : ℝ) := hrec.symm

/-- The middle estimate in Exercise 0.0.5. -/
theorem choose_le_sum_choose (n m : ℕ) :
    (n.choose m : ℝ) ≤ ∑ k ∈ range (m+1), (n.choose k : ℝ) := by
  exact single_le_sum (fun k _ => Nat.cast_nonneg _) (by simp)

/-- The upper estimate in Exercise 0.0.5. -/
theorem sum_choose_le_exp (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ k ∈ range (m+1), (n.choose k : ℝ)) ≤ (Real.exp 1 * n / m)^m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < m) hmn)
  let x : ℝ := m / n
  have hxpos : 0 < x := div_pos hmpos hnpos
  have hxle : x ≤ 1 := (div_le_one hnpos).2 (by exact_mod_cast hmn)
  have hweighted :
      (∑ k ∈ range (m+1), (n.choose k : ℝ)) * x^m ≤ (x+1)^n := by
    calc
      (∑ k ∈ range (m+1), (n.choose k : ℝ)) * x^m =
          ∑ k ∈ range (m+1), (n.choose k : ℝ) * x^m := by rw [sum_mul]
      _ ≤ ∑ k ∈ range (m+1), (n.choose k : ℝ) * x^k := by
        apply sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact pow_le_pow_of_le_one hxpos.le hxle (by simpa using mem_range.mp hk)
      _ ≤ ∑ k ∈ range (n+1), (n.choose k : ℝ) * x^k := by
        apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        intro i _ _
        positivity
      _ = (x+1)^n := by
        rw [add_pow]
        apply sum_congr rfl
        intro k hk
        simp only [one_pow]
        ring
  have hexp : (x+1)^n ≤ (Real.exp 1)^m := by
    calc
      (x+1)^n ≤ (Real.exp x)^n := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) n
      _ = Real.exp ((n : ℝ)*x) := (Real.exp_nat_mul x n).symm
      _ = Real.exp (m : ℝ) := by congr 1; dsimp [x]; field_simp
      _ = (Real.exp 1)^m := by simp [Real.exp_nat_mul]
  have hcancel : (Real.exp 1 * n / m)^m * x^m = (Real.exp 1)^m := by
    rw [← mul_pow]
    congr 1
    dsimp [x]
    field_simp
  apply (mul_le_mul_iff_left₀ (pow_pos hxpos m)).mp
  rw [hcancel]
  exact hweighted.trans hexp

/-- Exercise 0.0.5, all three inequalities in their original chain. -/
theorem exercise_0_0_5 (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((n : ℝ) / m)^m ≤ (n.choose m : ℝ) ∧
    (n.choose m : ℝ) ≤ ∑ k ∈ range (m+1), (n.choose k : ℝ) ∧
    (∑ k ∈ range (m+1), (n.choose k : ℝ)) ≤ (Real.exp 1 * n / m)^m :=
  ⟨pow_div_le_choose n m hmn, choose_le_sum_choose n m, sum_choose_le_exp n m hm hmn⟩

/-- The unordered selection count used in Exercise 0.0.6. -/
theorem unordered_selection_count (N k : ℕ) :
    Fintype.card (Sym (Fin N) k) = (N+k-1).choose k := by
  simpa using (Sym.card_sym_eq_choose (α := Fin N) k)

/-- A convenient slightly enlarged binomial upper bound for unordered samples. -/
theorem unordered_selection_bound (N k : ℕ) (hk : 1 ≤ k) :
    ((N+k-1).choose k : ℝ) ≤ (Real.exp 1 * (1 + (N : ℝ)/k))^k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    ((N+k-1).choose k : ℝ) ≤ ((N+k).choose k : ℝ) := by
      exact_mod_cast Nat.choose_le_choose k (Nat.sub_le (N+k) 1)
    _ ≤ ∑ j ∈ range (k+1), ((N+k).choose j : ℝ) := choose_le_sum_choose (N+k) k
    _ ≤ (Real.exp 1 * (N+k) / k)^k := by simpa only [Nat.cast_add] using sum_choose_le_exp (N+k) k hk (by omega)
    _ = (Real.exp 1 * (1 + (N : ℝ)/k))^k := by
      congr 1
      push_cast
      field_simp
      ring

/-- The estimate after choosing a sample size with `1 ≤ ε² k`. -/
theorem unordered_selection_epsilon_bound (N k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hεk : 1 ≤ ε^2 * k) :
    ((N+k-1).choose k : ℝ) ≤ (Real.exp 1 + Real.exp 1 * ε^2 * N)^k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : (N : ℝ)/k ≤ ε^2*N := by
    apply (div_le_iff₀ hkpos).2
    nlinarith [mul_le_mul_of_nonneg_right hεk (Nat.cast_nonneg N)]
  refine (unordered_selection_bound N k hk).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hratio (Real.exp_nonneg 1)]

#print axioms exercise_0_0_5
#print axioms unordered_selection_count
#print axioms unordered_selection_bound
#print axioms unordered_selection_epsilon_bound
end HDP
