/-
Finite-product perturbation bounds and the triangular-array product limit used
for the Poisson limit theorem.
-/
import Mathlib
import HDP.PoissonCharFun

open Finset Filter Topology Complex MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators

namespace HDP

lemma norm_prod_sub_prod_range_le (a b : ℕ → ℂ) (M : ℕ → ℝ) (hM : ∀ i, 1 ≤ M i) :
    ∀ N : ℕ, (∀ i < N, ‖a i‖ ≤ M i) → (∀ i < N, ‖b i‖ ≤ M i) →
      ‖∏ i ∈ range N, a i - ∏ i ∈ range N, b i‖ ≤
        (∏ i ∈ range N, M i) * ∑ i ∈ range N, ‖a i - b i‖
  | 0, _, _ => by simp
  | N+1, ha, hb => by
      rw [prod_range_succ, prod_range_succ, prod_range_succ, sum_range_succ]
      have haN : ‖a N‖ ≤ M N := ha N (Nat.lt_succ_self _)
      have hbN : ‖b N‖ ≤ M N := hb N (Nat.lt_succ_self _)
      have ha' : ∀ i < N, ‖a i‖ ≤ M i := fun i hi => ha i (Nat.lt_trans hi (Nat.lt_succ_self _))
      have hb' : ∀ i < N, ‖b i‖ ≤ M i := fun i hi => hb i (Nat.lt_trans hi (Nat.lt_succ_self _))
      have ih := norm_prod_sub_prod_range_le a b M hM N ha' hb'
      have hP : ‖∏ i ∈ range N, a i‖ ≤ ∏ i ∈ range N, M i := by
        calc
          ‖∏ i ∈ range N, a i‖ ≤ ∏ i ∈ range N, ‖a i‖ := norm_prod_le _ _
          _ ≤ ∏ i ∈ range N, M i := prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => ha' i (mem_range.mp hi))
      have hQ : ‖∏ i ∈ range N, b i‖ ≤ ∏ i ∈ range N, M i := by
        calc
          ‖∏ i ∈ range N, b i‖ ≤ ∏ i ∈ range N, ‖b i‖ := norm_prod_le _ _
          _ ≤ ∏ i ∈ range N, M i := prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => hb' i (mem_range.mp hi))
      have hWnonneg : 0 ≤ ∏ i ∈ range N, M i := prod_nonneg fun i _ => le_trans zero_le_one (hM i)
      have hWle : (∏ i ∈ range N, M i) ≤ ∏ i ∈ range (N+1), M i := by
        rw [prod_range_succ]
        exact le_mul_of_one_le_right hWnonneg (hM N)
      have hSnonneg : 0 ≤ ∑ i ∈ range N, ‖a i - b i‖ := sum_nonneg fun i _ => norm_nonneg _
      have hd : 0 ≤ ‖a N - b N‖ := norm_nonneg _
      have hD : ‖∏ i ∈ range N, a i - ∏ i ∈ range N, b i‖ ≤
          (∏ i ∈ range N, M i) * ∑ i ∈ range N, ‖a i - b i‖ := ih
      have hstep1 : ‖(∏ i ∈ range N, a i) * a N - (∏ i ∈ range N, b i) * b N‖ ≤
          (∏ i ∈ range N, M i) * ‖a N - b N‖ +
            M N * ‖∏ i ∈ range N, a i - ∏ i ∈ range N, b i‖ := by
        calc
          _ = ‖(∏ i ∈ range N, a i) * (a N - b N) +
                ((∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)) * b N‖ := by ring_nf
          _ ≤ ‖(∏ i ∈ range N, a i) * (a N - b N)‖ +
                ‖((∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)) * b N‖ := norm_add_le _ _
          _ = ‖∏ i ∈ range N, a i‖ * ‖a N - b N‖ +
                ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ * ‖b N‖ := by rw [norm_mul, norm_mul]
          _ ≤ (∏ i ∈ range N, M i) * ‖a N - b N‖ +
                M N * ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ := by
            have h1 : ‖∏ i ∈ range N, a i‖ * ‖a N - b N‖ ≤
                (∏ i ∈ range N, M i) * ‖a N - b N‖ :=
              mul_le_mul_of_nonneg_right hP hd
            have h2 : ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ * ‖b N‖ ≤
                ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ * M N :=
              mul_le_mul_of_nonneg_left hbN (norm_nonneg _)
            calc
              ‖∏ i ∈ range N, a i‖ * ‖a N - b N‖ +
                  ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ * ‖b N‖
                  ≤ (∏ i ∈ range N, M i) * ‖a N - b N‖ +
                    ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ * M N := add_le_add h1 h2
              _ = (∏ i ∈ range N, M i) * ‖a N - b N‖ +
                    M N * ‖(∏ i ∈ range N, a i) - (∏ i ∈ range N, b i)‖ := by ring
      have hDm : M N * ‖∏ i ∈ range N, a i - ∏ i ∈ range N, b i‖ ≤
          M N * ((∏ i ∈ range N, M i) * ∑ i ∈ range N, ‖a i - b i‖) :=
        mul_le_mul_of_nonneg_left hD (le_trans zero_le_one (hM N))
      have hWd : (∏ i ∈ range N, M i) * ‖a N - b N‖ ≤
          (∏ i ∈ range N, M i) * (M N * ‖a N - b N‖) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hM N, hd]) hWnonneg
      calc
        ‖(∏ i ∈ range N, a i) * a N - (∏ i ∈ range N, b i) * b N‖
            ≤ (∏ i ∈ range N, M i) * ‖a N - b N‖ +
              M N * ‖∏ i ∈ range N, a i - ∏ i ∈ range N, b i‖ := hstep1
        _ ≤ (∏ i ∈ range N, M i) * ‖a N - b N‖ +
              M N * ((∏ i ∈ range N, M i) * ∑ i ∈ range N, ‖a i - b i‖) := add_le_add le_rfl hDm
        _ ≤ (∏ i ∈ range N, M i) * (M N * ‖a N - b N‖) +
              M N * ((∏ i ∈ range N, M i) * ∑ i ∈ range N, ‖a i - b i‖) := add_le_add hWd le_rfl
        _ = (∏ i ∈ range N, M i) * M N *
              (‖a N - b N‖ + ∑ i ∈ range N, ‖a i - b i‖) := by ring_nf
        _ = (∏ i ∈ range N, M i) * M N *
              (∑ i ∈ range N, ‖a i - b i‖ + ‖a N - b N‖) := by ring


lemma norm_one_add_sub_exp_le {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(1 + u) - cexp u‖ ≤ (3/4 : ℝ) * ‖u‖^2 := by
  have h := Complex.exp_bound hu (n := 2) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one, div_one,
    zero_add] at h
  norm_num at h ⊢
  rw [norm_sub_rev]
  simpa [mul_comm] using h



lemma prod_exp_tendsto (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) Filter.atTop (𝓝 (lam:ℝ)))
    (t : ℝ) :
    Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N,
      cexp ((p N i : ℂ) * (cexp ((t:ℂ) * I) - 1))) Filter.atTop
      (𝓝 (cexp ((lam:ℂ) * (cexp ((t:ℂ) * I) - 1)))) := by
  have hsumC : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℂ)) Filter.atTop
      (𝓝 (lam:ℂ)) := by
    have := Complex.continuous_ofReal.tendsto (lam:ℝ) |>.comp hsum
    simpa [Function.comp_def] using this
  have hmul : Tendsto (fun N : ℕ => (cexp ((t:ℂ) * I) - 1) *
      (∑ i ∈ Finset.range N, (p N i : ℂ))) Filter.atTop
      (𝓝 ((cexp ((t:ℂ) * I) - 1) * (lam:ℂ))) := tendsto_const_nhds.mul hsumC
  have hexp : Tendsto (fun N : ℕ => cexp ((cexp ((t:ℂ) * I) - 1) *
      (∑ i ∈ Finset.range N, (p N i : ℂ)))) Filter.atTop
      (𝓝 (cexp ((cexp ((t:ℂ) * I) - 1) * (lam:ℂ)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hmul
  have hconv : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N,
      cexp ((p N i : ℂ) * (cexp ((t:ℂ) * I) - 1))) Filter.atTop
      (𝓝 (cexp ((cexp ((t:ℂ) * I) - 1) * (lam:ℂ)))) := by
    refine hexp.congr' ?_
    filter_upwards with N
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa [mul_comm] using hconv



lemma sum_sq_tendsto_zero (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop, ∀ i < N, (p N i : ℝ) < ε)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) Filter.atTop (𝓝 (lam:ℝ))) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, ((p N i : ℝ)^2)) Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / ((lam:ℝ) + 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ_le : δ * ((lam:ℝ) + 1) < ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [show (0:ℝ) ≤ (lam:ℝ) by positivity]
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hmax δ hδ)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hsum 1 (by norm_num)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hN1' : ∀ i < N, (p N i : ℝ) < δ := hN1 N (le_trans (le_max_left _ _) hN)
  have hN2' : dist (∑ i ∈ Finset.range N, (p N i : ℝ)) (lam:ℝ) < 1 :=
    hN2 N (le_trans (le_max_right _ _) hN)
  have hsum_lt : (∑ i ∈ Finset.range N, (p N i : ℝ)) < (lam:ℝ) + 1 := by
    rw [Real.dist_eq] at hN2'
    have hlt : (∑ i ∈ Finset.range N, (p N i : ℝ)) - (lam:ℝ) < 1 := (abs_lt.mp hN2').2
    linarith
  have hsq_le : ∑ i ∈ Finset.range N, ((p N i : ℝ)^2) ≤
      δ * ∑ i ∈ Finset.range N, (p N i : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hpi : 0 ≤ (p N i : ℝ) := (p N i).coe_nonneg
    have hlt : (p N i : ℝ) < δ := hN1' i (Finset.mem_range.mp hi)
    nlinarith
  have hsq_nonneg : 0 ≤ ∑ i ∈ Finset.range N, ((p N i : ℝ)^2) :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hlt : ∑ i ∈ Finset.range N, ((p N i : ℝ)^2) < ε := by
    calc
      _ ≤ δ * ∑ i ∈ Finset.range N, (p N i : ℝ) := hsq_le
      _ ≤ δ * ((lam:ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hsum_lt.le hδ.le
      _ < ε := hδ_le
  simpa [Real.dist_eq, abs_of_nonneg hsq_nonneg] using hlt



lemma norm_one_add_le_exp_norm (u : ℂ) : ‖1 + u‖ ≤ Real.exp ‖u‖ := by
  calc
    ‖1 + u‖ ≤ ‖(1:ℂ)‖ + ‖u‖ := norm_add_le _ _
    _ = 1 + ‖u‖ := by simp
    _ ≤ Real.exp ‖u‖ := by
      simpa [add_comm] using Real.add_one_le_exp ‖u‖

lemma norm_exp_le_exp_norm (u : ℂ) : ‖cexp u‖ ≤ Real.exp ‖u‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (Complex.re_le_norm u)



lemma prod_diff_tendsto_zero (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0) (t : ℝ)
    (hp : ∀ N i, p N i ≤ 1)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop, ∀ i < N, (p N i : ℝ) < ε)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) Filter.atTop (𝓝 (lam:ℝ))) :
    Tendsto (fun N : ℕ =>
      ‖∏ i ∈ Finset.range N, (1 + (p N i : ℂ) * (cexp ((t:ℂ) * I) - 1)) -
        ∏ i ∈ Finset.range N, cexp ((p N i : ℂ) * (cexp ((t:ℂ) * I) - 1))‖)
      Filter.atTop (𝓝 0) := by
  let w : ℂ := cexp ((t:ℂ) * I) - 1
  let c : ℝ := ‖w‖
  let u : ℕ → ℕ → ℂ := fun N i => (p N i : ℂ) * w
  let M : ℕ → ℕ → ℝ := fun N i => Real.exp (c * (p N i : ℝ))
  have hc : 0 ≤ c := norm_nonneg _
  have hM1 : ∀ N i, 1 ≤ M N i := fun N i => Real.one_le_exp (by positivity)
  have ha : ∀ N i, ‖1 + u N i‖ ≤ M N i := by
    intro N i
    calc
      ‖1 + u N i‖ ≤ Real.exp ‖u N i‖ := norm_one_add_le_exp_norm _
      _ = M N i := by
        simp only [u, M, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p N i).coe_nonneg]
        rw [mul_comm]
  have hb : ∀ N i, ‖cexp (u N i)‖ ≤ M N i := by
    intro N i
    calc
      ‖cexp (u N i)‖ ≤ Real.exp ‖u N i‖ := norm_exp_le_exp_norm _
      _ = M N i := by
        simp only [u, M, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p N i).coe_nonneg]
        rw [mul_comm]
  have hD : ∀ N, ‖∏ i ∈ Finset.range N, (1 + u N i) - ∏ i ∈ Finset.range N, cexp (u N i)‖ ≤
      (∏ i ∈ Finset.range N, M N i) * ∑ i ∈ Finset.range N, ‖(1 + u N i) - cexp (u N i)‖ :=
    fun N => norm_prod_sub_prod_range_le (fun i => 1 + u N i) (fun i => cexp (u N i))
      (M N) (hM1 N) N (fun i _ => ha N i) (fun i _ => hb N i)
  have hC : 0 ≤ (3/4 : ℝ) * c^2 := by positivity
  have hpoint : ∀ᶠ N : ℕ in Filter.atTop,
      ∑ i ∈ Finset.range N, ‖(1 + u N i) - cexp (u N i)‖ ≤
        ((3/4 : ℝ) * c^2) * ∑ i ∈ Finset.range N, ((p N i : ℝ)^2) := by
    have hε : 0 < 1 / (c + 1) := by positivity
    filter_upwards [hmax (1 / (c + 1)) hε] with N hN
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hpi : 0 ≤ (p N i : ℝ) := (p N i).coe_nonneg
    have hp_lt : (p N i : ℝ) < 1 / (c + 1) := hN i (Finset.mem_range.mp hi)
    have hnorm : ‖u N i‖ = c * (p N i : ℝ) := by
      simp only [u, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi]
      rw [mul_comm]
    have hle1 : ‖u N i‖ ≤ 1 := by
      rw [hnorm]
      have : c * (p N i : ℝ) ≤ c * (1 / (c + 1)) :=
        mul_le_mul_of_nonneg_left hp_lt.le hc
      have hc1 : c * (1 / (c + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
      linarith
    calc
      ‖(1 + u N i) - cexp (u N i)‖ ≤ (3/4 : ℝ) * ‖u N i‖^2 := norm_one_add_sub_exp_le hle1
      _ = ((3/4 : ℝ) * c^2) * (p N i : ℝ)^2 := by rw [hnorm]; ring
  have hS : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, ‖(1 + u N i) - cexp (u N i)‖)
      Filter.atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun i hi => norm_nonneg _)
      hpoint ?_
    have hsq := sum_sq_tendsto_zero p lam hmax hsum
    simpa using hsq.const_mul ((3/4 : ℝ) * c^2)
  have hWbound : ∀ᶠ N : ℕ in Filter.atTop,
      (∏ i ∈ Finset.range N, M N i) ≤ Real.exp (c * ((lam:ℝ) + 1)) := by
    filter_upwards [hsum.eventually (Iio_mem_nhds (by linarith : (lam:ℝ) < (lam:ℝ) + 1))] with N hN
    have hprod : (∏ i ∈ Finset.range N, M N i) =
        Real.exp (c * ∑ i ∈ Finset.range N, (p N i : ℝ)) := by
      simp only [M]
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    rw [hprod]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hN.le hc)
  have hbound : ∀ᶠ N : ℕ in Filter.atTop,
      ‖∏ i ∈ Finset.range N, (1 + u N i) - ∏ i ∈ Finset.range N, cexp (u N i)‖ ≤
        Real.exp (c * ((lam:ℝ) + 1)) * (((3/4 : ℝ) * c^2) *
          ∑ i ∈ Finset.range N, ((p N i : ℝ)^2)) := by
    filter_upwards [hpoint, hWbound] with N hN hW
    calc
      _ ≤ (∏ i ∈ Finset.range N, M N i) * ∑ i ∈ Finset.range N, ‖(1 + u N i) - cexp (u N i)‖ := hD N
      _ ≤ Real.exp (c * ((lam:ℝ) + 1)) * (((3/4 : ℝ) * c^2) *
          ∑ i ∈ Finset.range N, ((p N i : ℝ)^2)) := by
        gcongr
      _ = Real.exp (c * ((lam:ℝ) + 1)) * (((3/4 : ℝ) * c^2) *
          ∑ i ∈ Finset.range N, ((p N i : ℝ)^2)) := rfl
  have hRHS : Tendsto (fun N : ℕ => Real.exp (c * ((lam:ℝ) + 1)) *
      (((3/4 : ℝ) * c^2) * ∑ i ∈ Finset.range N, ((p N i : ℝ)^2))) Filter.atTop (𝓝 0) := by
    have hsq := sum_sq_tendsto_zero p lam hmax hsum
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.mul hsq)
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) hbound ?_
  simpa [u] using hRHS



theorem poisson_product_tendsto (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0) (t : ℝ)
    (hp : ∀ N i, p N i ≤ 1)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop, ∀ i < N, (p N i : ℝ) < ε)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) Filter.atTop (𝓝 (lam:ℝ))) :
    Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N,
      ((1 - (p N i : ℂ)) + (p N i : ℂ) * cexp ((t:ℂ) * I))) Filter.atTop
      (𝓝 (cexp ((lam:ℂ) * (cexp ((t:ℂ) * I) - 1)))) := by
  let z : ℂ := cexp ((t:ℂ) * I)
  have hdiff := prod_diff_tendsto_zero p lam t hp hmax hsum
  have hdiff0 : Tendsto (fun N : ℕ =>
      ∏ i ∈ Finset.range N, (1 + (p N i : ℂ) * (cexp ((t:ℂ) * I) - 1)) -
        ∏ i ∈ Finset.range N, cexp ((p N i : ℂ) * (cexp ((t:ℂ) * I) - 1))) Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hdiff
  have hexp := prod_exp_tendsto p lam hsum t
  have hsumt := hdiff0.add hexp
  have hsumt' : Tendsto (fun N : ℕ =>
      (∏ i ∈ Finset.range N, (1 + (p N i : ℂ) * (cexp ((t:ℂ) * I) - 1)) -
        ∏ i ∈ Finset.range N, cexp ((p N i : ℂ) * (cexp ((t:ℂ) * I) - 1))) +
        ∏ i ∈ Finset.range N, cexp ((p N i : ℂ) * (cexp ((t:ℂ) * I) - 1)))
      Filter.atTop (𝓝 (cexp ((lam:ℂ) * (cexp ((t:ℂ) * I) - 1)))) := by
    simpa [zero_add] using hsumt
  refine hsumt'.congr' ?_
  filter_upwards with N
  rw [sub_add_cancel]
  apply Finset.prod_congr rfl
  intro i hi
  ring

end HDP
