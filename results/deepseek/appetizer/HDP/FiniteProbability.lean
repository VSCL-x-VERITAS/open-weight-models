/-
Finite probability tools used in the empirical method of Maurey:
weighted finite measures, marginal integrals, the scalar variance identity
for independent mean-zero variables, and the vector identity of Exercise
0.0.3(a).

This file uses only Mathlib.
-/
import Mathlib

open Set BigOperators MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace InnerProductSpace
set_option maxHeartbeats 1000000

namespace HDP
noncomputable def weightPMF {m : ℕ} (lam : Fin m → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    PMF (Fin m) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (lam i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i)]
    simp [h1])

lemma weightPMF_real {m : ℕ} (lam : Fin m → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) (i : Fin m) :
    (weightPMF lam h0 h1).toMeasure.real {i} = lam i := by
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  simp [weightPMF, ENNReal.toReal_ofReal (h0 i)]

lemma integral_weightPMF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : ℕ} (lam : Fin m → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1)
    (f : Fin m → E) :
    ∫ i, f i ∂(weightPMF lam h0 h1).toMeasure = ∑ i, lam i • f i := by
  rw [integral_fintype f (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weightPMF_real]

lemma product_integral_weight {m k : ℕ} (lam : Fin m → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1)
    (F : (Fin k → Fin m) → ℝ) :
    ∫ ω : Fin k → Fin m, F ω ∂(Measure.pi (fun _ : Fin k => (weightPMF lam h0 h1).toMeasure))
      = ∑ ω, (∏ i, lam (ω i)) * F ω := by
  rw [integral_fintype F (Integrable.of_finite)]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ω hω
  congr 1
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  simp [weightPMF, ENNReal.toReal_ofReal (h0 _)]

lemma marginal_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m k : ℕ} (lam : Fin m → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1)
    (f : Fin m → E) (j : Fin k) :
    ∫ ω : Fin k → Fin m, f (ω j) ∂(Measure.pi (fun _ : Fin k => (weightPMF lam h0 h1).toMeasure))
      = ∫ a, f a ∂(weightPMF lam h0 h1).toMeasure := by
  have hmap : (Measure.pi (fun _ : Fin k => (weightPMF lam h0 h1).toMeasure)).map (fun ω => ω j)
      = (weightPMF lam h0 h1).toMeasure :=
    (measurePreserving_eval (fun _ : Fin k => (weightPMF lam h0 h1).toMeasure) j).map_eq
  calc
    ∫ ω : Fin k → Fin m, f (ω j) ∂(Measure.pi (fun _ : Fin k => (weightPMF lam h0 h1).toMeasure))
        = ∫ a, f a ∂((Measure.pi (fun _ : Fin k => (weightPMF lam h0 h1).toMeasure)).map (fun ω => ω j)) := by
          exact (integral_map (measurable_pi_apply j).aemeasurable (by fun_prop)).symm
    _ = ∫ a, f a ∂(weightPMF lam h0 h1).toMeasure := by rw [hmap]

lemma weighted_variance_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (lam : Fin m → ℝ) (z : Fin m → E) (x : E)
    (hlam1 : ∑ i, lam i = 1)
    (hx : ∑ i, lam i • z i = x) :
    (∑ i, lam i * ‖z i - x‖ ^ 2) = (∑ i, lam i * ‖z i‖ ^ 2) - ‖x‖ ^ 2 := by
  have hterm : ∀ i, ‖z i - x‖ ^ 2 = (‖z i‖ ^ 2 - 2 * ⟪z i, x⟫_ℝ + ‖x‖ ^ 2) := by
    intro i; rw [norm_sub_sq_real]
  have hinner : ∑ i, lam i * ⟪z i, x⟫_ℝ = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq x, ← hx, sum_inner]
    simp [inner_smul_left]
  have hpoint : ∀ i, lam i * (‖z i‖ ^ 2 - 2 * ⟪z i, x⟫_ℝ + ‖x‖ ^ 2) =
      (lam i * ‖z i‖ ^ 2 - lam i * (2 * ⟪z i, x⟫_ℝ) + lam i * ‖x‖ ^ 2) := by
    intro i; ring
  simp_rw [hterm, hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ i, lam i * (2 * ⟪z i, x⟫_ℝ) = 2 * ‖x‖ ^ 2 := by
    rw [← hinner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h2 : ∑ i, lam i * ‖x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← Finset.sum_mul, hlam1, one_mul]
  rw [h1, h2]
  ring

lemma exists_le_of_sum_mul_le {ι : Type*} [Fintype ι] {W F : ι → ℝ} {c : ℝ}
    (hW0 : ∀ i, 0 ≤ W i) (hW1 : ∑ i, W i = 1) (h : ∑ i, W i * F i ≤ c) :
    ∃ i, F i ≤ c := by
  by_contra hc
  push_neg at hc
  obtain ⟨j, hj⟩ : ∃ j, 0 < W j := by
    by_contra h'
    push_neg at h'
    have : ∑ i, W i ≤ 0 := Finset.sum_nonpos fun i _ => h' i
    linarith
  have hlt : ∑ i, W i * c < ∑ i, W i * F i := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact mul_le_mul_of_nonneg_left (le_of_lt (hc i)) (hW0 i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (hc j) hj⟩
  have hleft : ∑ i, W i * c = c := by
    rw [← Finset.sum_mul, hW1, one_mul]
  rw [hleft] at hlt
  linarith

lemma integral_sq_sum_of_indep_mean_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Set.Pairwise Set.univ fun i j => X i ⟂ᵢ[μ] X j)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    ∫ ω, (∑ i, X i ω) ^ 2 ∂μ = ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ := by
  have hvar := IndepFun.variance_sum (μ := μ) (s := Finset.univ) (X := X)
    (fun i _ => hX i) (by simpa [Set.Pairwise] using hind)
  have hmean_sum : ∫ ω, (∑ i, X i ω) ∂μ = 0 := by
    rw [integral_finset_sum]
    · simp [hmean]
    · intro i hi; exact (hX i).integrable (by norm_num)
  have hmeas : AEMeasurable (fun ω => ∑ i, X i ω) μ := by
    convert (Finset.aemeasurable_sum Finset.univ fun i _ => (hX i).aemeasurable) using 1
    ext ω; simp
  have hvar_sum := variance_of_integral_eq_zero (μ := μ) (X := fun ω => ∑ i, X i ω) hmeas hmean_sum
  have hvar_each : ∀ i, variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ := by
    intro i
    exact variance_of_integral_eq_zero (hX i).aemeasurable (hmean i)
  have hvar' : variance (fun ω => ∑ i, X i ω) μ = ∑ i, variance (X i) μ := by
    convert hvar using 2
    ext ω; simp
  rw [hvar_sum] at hvar'
  simpa [hvar_each] using hvar'

lemma integral_norm_sq_sum_of_indep_mean_zero {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Fin k → Ω → EuclideanSpace ℝ (Fin n))
    (hW : ∀ j, MemLp (W j) 2 μ)
    (hind : iIndepFun W μ)
    (hmean : ∀ j, ∫ ω, W j ω ∂μ = 0) :
    ∫ ω, ‖∑ j, W j ω‖ ^ 2 ∂μ = ∑ j, ∫ ω, ‖W j ω‖ ^ 2 ∂μ := by
  let X : Fin k → Fin n → Ω → ℝ := fun j l ω => (W j ω).ofLp l
  have hX : ∀ j l, MemLp (X j l) 2 μ := by
    intro j l
    refine (hW j).of_le ?_ ?_
    · exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) l).comp_aestronglyMeasurable
        (hW j).aestronglyMeasurable
    · filter_upwards with ω
      exact PiLp.norm_apply_le (W j ω) l
  have hXind : ∀ l, Set.Pairwise Set.univ fun i j => X i l ⟂ᵢ[μ] X j l := by
    intro l i _ j _ hij
    exact (hind.indepFun hij).comp
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) l).measurable
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) l).measurable
  have hXmean : ∀ j l, ∫ ω, X j l ω ∂μ = 0 := by
    intro j l
    have h := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n => ℝ) l).integral_comp_comm
      ((hW j).integrable (by norm_num))
    rw [show ∫ ω, W j ω l ∂μ = (∫ ω, W j ω ∂μ) l from by simpa using h]
    rw [hmean j]
    rfl
  have hscalar : ∀ l, ∫ ω, (∑ j, X j l ω) ^ 2 ∂μ = ∑ j, ∫ ω, (X j l ω) ^ 2 ∂μ := by
    intro l
    exact integral_sq_sum_of_indep_mean_zero (X := fun j => X j l)
      (fun j => hX j l) (hXind l) (fun j => hXmean j l)
  have hnorm : ∀ ω, ‖∑ j, W j ω‖ ^ 2 = ∑ l, (∑ j, X j l ω) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro l hl
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rw [Real.norm_eq_abs, sq_abs]
  have hsum_norm : ∀ j, ∫ ω, ‖W j ω‖ ^ 2 ∂μ = ∫ ω, ∑ l, (X j l ω) ^ 2 ∂μ := by
    intro j
    congr 1
    ext ω
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Real.norm_eq_abs, sq_abs]
  calc
    ∫ ω, ‖∑ j, W j ω‖ ^ 2 ∂μ = ∫ ω, ∑ l, (∑ j, X j l ω) ^ 2 ∂μ := by
      simp_rw [hnorm]
    _ = ∑ l, ∫ ω, (∑ j, X j l ω) ^ 2 ∂μ := by
      rw [integral_finset_sum]
      intro l hl
      exact (memLp_finset_sum Finset.univ (fun j _ => hX j l)).integrable_sq
    _ = ∑ l, ∑ j, ∫ ω, (X j l ω) ^ 2 ∂μ := by
      simp_rw [hscalar]
    _ = ∑ j, ∑ l, ∫ ω, (X j l ω) ^ 2 ∂μ := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∫ ω, ∑ l, (X j l ω) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finset_sum]
      intro l hl
      exact (hX j l).integrable_sq
    _ = ∑ j, ∫ ω, ‖W j ω‖ ^ 2 ∂μ := by
      simp_rw [hsum_norm]


end HDP
