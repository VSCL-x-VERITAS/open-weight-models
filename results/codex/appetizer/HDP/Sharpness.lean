import HDP.EntropyPacking
import HDP.EntropyParameters
import HDP.EntropyEmbedding

namespace HDP.Sharpness

/-- Assisted continuation 001: the operator's explicit dyadic entropy lower
bound for diameter-one crosspolytopes, with arbitrary ambient covering centers. -/
theorem entropy_lower_bound :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ ε : ℝ, 0 < ε →
        ε < c * min 1 (Real.sqrt (Real.log (1 + (n : ℝ) / (k : ℝ)) / (k : ℝ))) →
      ∀ C : Finset (HDP.Crosspolytope.Space n),
        HDP.BallCover (HDP.Crosspolytope.body n) ε C →
        2 ^ (k - 1) < C.card := by
  refine ⟨radiusConstant, radiusConstant_pos, radiusConstant_lt_one, ?_⟩
  intro n _hn k hk hkn ε hε hsmall C hcover
  have hs : ε < radiusConstant * min 1 (Real.sqrt (logScale n k / (k : ℝ))) := hsmall
  rcases parameter_dichotomy hk hkn hε hs with ⟨_, hdense⟩ | ⟨m, q, hm, hq, hdim, hrate, hrad⟩
  · obtain ⟨A, hsep, hcard⟩ := HDP.exists_dense_hamming_code k hk
    exact hcard.trans_le
      (HDP.Crosspolytope.dense_code_card_le_cover_card hk hkn ε hε.le hdense A hsep C hcover)
  · obtain ⟨A, hsep, hcard⟩ := HDP.exists_sparse_hamming_code m q k (by omega) hrate
    exact hcard.trans_le
      (HDP.Crosspolytope.sparse_code_card_le_cover_card hm (by omega) hdim ε hε.le
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrad) A hsep C hcover)

/-- The previously proved Exercise 0.0.6 upper bound on the same family.
The geometry module proves that these `2*n` generators are the actual vertices. -/
theorem crosspolytope_upper_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Finset (HDP.Crosspolytope.Space n),
      HDP.BallCover (HDP.Crosspolytope.body n) ε C ∧
      (C.card : ℝ) ≤ (Real.exp 1 + Real.exp 1 * ε ^ 2 * (2 * n)) ^ ⌈1 / ε ^ 2⌉₊ := by
  obtain ⟨C, hcover, _, hbound⟩ := HDP.improved_covering
    (HDP.Crosspolytope.vertices n) ε hε (by
      intro x hx y hy
      simpa [dist_eq_norm] using HDP.Crosspolytope.dist_body_le_one hx hy)
  refine ⟨C, hcover, ?_⟩
  simpa [HDP.Crosspolytope.card_vertices] using hbound

end HDP.Sharpness
