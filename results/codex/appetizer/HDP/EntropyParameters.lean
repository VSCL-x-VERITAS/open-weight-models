import Mathlib

namespace HDP.Sharpness

noncomputable section

set_option maxHeartbeats 800000

def radiusConstant : ℝ := 1 / 1000000

def logScale (n k : ℕ) : ℝ := Real.log (1 + (n : ℝ) / k)

lemma radiusConstant_pos : 0 < radiusConstant := by norm_num [radiusConstant]

lemma radiusConstant_lt_one : radiusConstant < 1 := by norm_num [radiusConstant]

lemma logScale_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    0 < logScale n k := by
  apply Real.log_pos
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le hk' (by exact_mod_cast hkn)
  exact lt_add_of_pos_right _ (div_pos hn' hk')

lemma radius_square_bounds {n k : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hε : 0 < ε)
    (hsmall : ε < radiusConstant * min 1 (Real.sqrt (logScale n k / k))) :
    ε ^ 2 < radiusConstant ^ 2 ∧
      ε ^ 2 * (k : ℝ) < radiusConstant ^ 2 * logScale n k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hL := logScale_pos hk hkn
  have h1 : ε < radiusConstant := by
    calc
      ε < radiusConstant * min 1 (Real.sqrt (logScale n k / k)) := hsmall
      _ ≤ radiusConstant * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) radiusConstant_pos.le
      _ = radiusConstant := mul_one _
  have h2 : ε < radiusConstant * Real.sqrt (logScale n k / k) :=
    hsmall.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) radiusConstant_pos.le)
  have hs : 0 ≤ Real.sqrt (logScale n k / k) := Real.sqrt_nonneg _
  have hsq : ε ^ 2 < (radiusConstant * Real.sqrt (logScale n k / k)) ^ 2 :=
    (sq_lt_sq₀ hε.le (mul_nonneg radiusConstant_pos.le hs)).2 h2
  rw [mul_pow, Real.sq_sqrt (div_nonneg hL.le hk'.le)] at hsq
  constructor
  · exact (sq_lt_sq₀ hε.le radiusConstant_pos.le).2 h1
  · have := mul_lt_mul_of_pos_right hsq hk'
    simpa [div_mul_cancel₀ _ (ne_of_gt hk'), mul_assoc] using this

lemma logScale_dense_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hR : (n : ℝ) / k ≤ 2 ^ 32) : logScale n k ≤ 33 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le hk' (by exact_mod_cast hkn)
  have harg : 1 + (n : ℝ) / k ≤ (2 : ℝ) ^ 33 := by norm_num at *; linarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + (n : ℝ) / k) harg
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_pow] at hlog
  norm_num at hlog htwo
  change Real.log (1 + (n : ℝ) / k) ≤ 33
  exact hlog.trans (by simpa using mul_le_mul_of_nonneg_left htwo (by norm_num : (0 : ℝ) ≤ 33))

lemma logScale_sparse_bound {n k : ℕ}
    (hR : (2 : ℝ) ^ 32 < (n : ℝ) / k) : 16 < logScale n k := by
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have harg : (2 : ℝ) ^ 32 < 1 + (n : ℝ) / k := by linarith
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ 32) harg
  rw [Real.log_pow] at hlog
  norm_num at hlog htwo
  dsimp [logScale]
  linarith

lemma sparse_parameters {n k : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hε : 0 < ε)
    (hsmall : ε < radiusConstant * min 1 (Real.sqrt (logScale n k / k)))
    (hR : (2 : ℝ) ^ 32 < (n : ℝ) / k) :
    ∃ m q : ℕ, 1 ≤ m ∧ 64 ≤ q ∧ (2 * m) * q ≤ n ∧
      2 ^ (k - 1 + 2 * m) < q ^ m ∧ 16 * ε ^ 2 * ((2 * m : ℕ) : ℝ) < 1 := by
  let L := logScale n k
  let R := (n : ℝ) / k
  let m : ℕ := ⌈4 * (k : ℝ) / L⌉₊
  let d : ℕ := 2 * m
  let q : ℕ := ⌊(n : ℝ) / d⌋₊
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hL : 16 < L := logScale_sparse_bound hR
  have hLpos : 0 < L := by linarith
  have hm : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmlo : 4 * (k : ℝ) / L ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < 4 * (k : ℝ) / L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmLlo : 4 * (k : ℝ) ≤ (m : ℝ) * L := (div_le_iff₀ hLpos).mp hmlo
  have hmLhi : (m : ℝ) * L < 4 * (k : ℝ) + L := by
    have := (mul_lt_mul_of_pos_right hmhi hLpos)
    field_simp at this
    nlinarith
  have hdpos : (0 : ℝ) < d := by dsimp [d]; positivity
  have hdeq : (d : ℝ) = 2 * (m : ℝ) := by simp [d]
  have hdle : (d : ℝ) ≤ 10 * (k : ℝ) := by
    have hprod : (m : ℝ) * 1 ≤ (m : ℝ) * L :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ L) (by positivity)
    have hmul := mul_nonneg (by linarith : 0 ≤ (m : ℝ) - 1) (by linarith : 0 ≤ L - 16)
    nlinarith
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hqlo : (q : ℝ) ≤ (n : ℝ) / d := Nat.floor_le (by positivity)
  have hqhi : (n : ℝ) / d < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdq : d * q ≤ n := by
    have := (le_div_iff₀ hdpos).mp hqlo
    exact_mod_cast (by simpa [mul_comm] using this : (d : ℝ) * q ≤ n)
  have hnd : (n : ℝ) < (d : ℝ) * ((q : ℝ) + 1) := by
    simpa [mul_comm] using (div_lt_iff₀ hdpos).mp hqhi
  have hRk : R * (k : ℝ) = n := div_mul_cancel₀ _ (ne_of_gt hkpos)
  have hRlarge : (4294967296 : ℝ) < R := by norm_num [R] at *; exact hR
  have hRq : R < 10 * ((q : ℝ) + 1) := by
    have hprod := mul_le_mul_of_nonneg_right hdle (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)
    nlinarith
  have hqR : R / 20 < (q : ℝ) := by linarith
  have hq64 : 64 ≤ q := by exact_mod_cast (by linarith : (64 : ℝ) ≤ q)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 64) hq64)
  have hqsq : 16 * (1 + R) ≤ (q : ℝ) ^ 2 := by
    have hs := (sq_lt_sq₀ (by linarith : 0 ≤ R / 20) hqpos.le).2 hqR
    nlinarith [sq_nonneg (R - 10000)]
  have hlogq : 4 * Real.log 2 + L ≤ 2 * Real.log (q : ℝ) := by
    have hlog := Real.log_le_log (by positivity : 0 < 16 * (1 + R)) hqsq
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by linarith : 1 + R ≠ 0), Real.log_pow] at hlog
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      convert (Real.log_pow (2 : ℝ) 4) using 1
      norm_num
    rw [h16] at hlog
    exact hlog
  have htwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlogstrict : ((k : ℝ) - 1 + 2 * (m : ℝ)) * Real.log 2 <
      (m : ℝ) * Real.log (q : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_left hlogq (by positivity : (0 : ℝ) ≤ m)
    have hkk := mul_nonneg (by linarith : 0 ≤ (k : ℝ) - 1) (by linarith : 0 ≤ 1 - Real.log 2)
    nlinarith
  have hpow : 2 ^ (k - 1 + 2 * m) < q ^ m := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (k - 1 + 2 * m) := by positivity
    have hr : Real.log ((2 : ℝ) ^ (k - 1 + 2 * m)) < Real.log ((q : ℝ) ^ m) := by
      simpa [Real.log_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk] using hlogstrict
    have := (Real.log_lt_log_iff hp (by positivity : (0 : ℝ) < (q : ℝ) ^ m)).mp hr
    exact_mod_cast this
  obtain ⟨hb1, hb2⟩ := radius_square_bounds hk hkn hε hsmall
  change ε ^ 2 * (k : ℝ) < radiusConstant ^ 2 * L at hb2
  have hrad : 16 * ε ^ 2 * (d : ℝ) < 1 := by
    have h1 := mul_lt_mul_of_pos_right hmLhi (sq_pos_of_pos hε)
    have h2 := mul_lt_mul_of_pos_right hb1 hLpos
    have h3 : ε ^ 2 * (d : ℝ) < 10 * radiusConstant ^ 2 := by
      apply (mul_lt_mul_iff_right₀ hLpos).mp
      rw [hdeq]
      nlinarith only [h1, h2, hb2]
    norm_num [radiusConstant] at h3
    nlinarith
  exact ⟨m, q, hm, hq64, hdq, hpow, hrad⟩

theorem parameter_dichotomy {n k : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hε : 0 < ε)
    (hsmall : ε < radiusConstant * min 1 (Real.sqrt (logScale n k / k))) :
    ((n : ℝ) / k ≤ 2 ^ 32 ∧ 32 * ε ^ 2 * (k : ℝ) * (64 : ℝ) ^ 2 < 1) ∨
    (∃ m q : ℕ, 1 ≤ m ∧ 64 ≤ q ∧ (2 * m) * q ≤ n ∧
      2 ^ (k - 1 + 2 * m) < q ^ m ∧ 16 * ε ^ 2 * ((2 * m : ℕ) : ℝ) < 1) := by
  by_cases hR : (n : ℝ) / k ≤ 2 ^ 32
  · left
    refine ⟨hR, ?_⟩
    have hsq := (radius_square_bounds hk hkn hε hsmall).2
    have hL := logScale_dense_bound hk hkn hR
    have hc : radiusConstant ^ 2 * logScale n k ≤ radiusConstant ^ 2 * 33 :=
      mul_le_mul_of_nonneg_left hL (sq_nonneg _)
    norm_num [radiusConstant] at hsq hc
    nlinarith
  · exact Or.inr (sparse_parameters hk hkn hε hsmall (lt_of_not_ge hR))

end
end HDP.Sharpness
