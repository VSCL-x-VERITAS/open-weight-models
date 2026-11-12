import HDP.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace HDP

/-- The law is on indices, so equal geometric points are permitted. -/
noncomputable def finiteIndexLaw {m : ℕ} (w : Fin m → ℝ≥0)
    (hw : ∑ i, w i = 1) : PMF (Fin m) :=
  PMF.ofFintype (fun i => (w i : ℝ≥0∞)) (by rw [← ENNReal.coe_finset_sum, hw]; rfl)

theorem finiteIndexLaw_singleton {m : ℕ} (w : Fin m → ℝ≥0)
    (hw : ∑ i, w i = 1) (i : Fin m) :
    (finiteIndexLaw w hw).toMeasure {i} = (w i : ℝ≥0∞) := by
  simp [finiteIndexLaw]

theorem finiteIndexLaw_value_probability {m n : ℕ} (w : Fin m → ℝ≥0)
    (hw : ∑ i, w i = 1) (z : Fin m → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) :
    (finiteIndexLaw w hw).toMeasure {i | z i = a} =
      ∑ i with z i = a, (w i : ℝ≥0∞) := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  simp [finiteIndexLaw, Finset.sum_filter, Set.indicator_apply]

theorem finiteIndexLaw_expectation {m n : ℕ} (w : Fin m → ℝ≥0)
    (hw : ∑ i, w i = 1) (z : Fin m → EuclideanSpace ℝ (Fin n)) :
    (∫ i, z i ∂(finiteIndexLaw w hw).toMeasure) = ∑ i, (w i : ℝ) • z i := by
  rw [PMF.integral_eq_sum]
  simp [finiteIndexLaw]

theorem finiteIndexLaw_memLp {m n : ℕ} (w : Fin m → ℝ≥0)
    (hw : ∑ i, w i = 1) (z : Fin m → EuclideanSpace ℝ (Fin n)) :
    MemLp z 2 (finiteIndexLaw w hw).toMeasure := MemLp.of_discrete

/-- Finite-support independent copies, with the correct index law and expectation. -/
theorem exists_finite_law_independent_copies {m n : ℕ} (w : Fin m → ℝ≥0)
    (hw : ∑ i, w i = 1) (z : Fin m → EuclideanSpace ℝ (Fin n)) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ I : ℕ → Ω → Fin m,
      (∀ j, HasLaw (I j) (finiteIndexLaw w hw).toMeasure P) ∧
      iIndepFun (fun j ω => z (I j ω)) P ∧
      (∀ j, IdentDistrib (fun ω => z (I j ω)) (fun ω => z (I 0 ω)) P P) ∧
      (∀ j, MemLp (fun ω => z (I j ω)) 2 P) ∧
      (∀ j, (∫ ω, z (I j ω) ∂P) = ∑ i, (w i : ℝ) • z i) ∧
      IsProbabilityMeasure P := by
  obtain ⟨Ω, mΩ, P, I, hmeas, hI, hind, hP⟩ :=
    exists_iid ℕ (finiteIndexLaw w hw).toMeasure
  letI := mΩ
  letI := hP
  have hident : ∀ j, IdentDistrib (I j) (I 0) P P := fun j =>
    ⟨(hI j).aemeasurable, (hI 0).aemeasurable,
      (hI j).map_eq.trans (hI 0).map_eq.symm⟩
  refine ⟨Ω, mΩ, P, I, hI,
    hind.comp (fun _ => z) (fun _ => measurable_of_finite _),
    fun j => (hident j).comp (measurable_of_finite z), ?_, ?_, hP⟩
  · intro j
    have hfmap : MemLp z 2 (P.map (I j)) := by
      rw [(hI j).map_eq]
      exact finiteIndexLaw_memLp w hw z
    exact hfmap.comp_of_map (hI j).aemeasurable
  · intro j
    exact ((hI j).integral_comp (finiteIndexLaw_memLp w hw z).aestronglyMeasurable).trans
      (finiteIndexLaw_expectation w hw z)

/-- Independent copies of any Euclidean probability law exist. -/
theorem exists_independent_copies {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ Z : ℕ → Ω → EuclideanSpace ℝ (Fin n),
      (∀ j, Measurable (Z j)) ∧ (∀ j, HasLaw (Z j) ν P) ∧
        iIndepFun Z P ∧ IsProbabilityMeasure P :=
  exists_iid ℕ ν

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_centered_eq_zero {n : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hZ : MemLp Z 2 μ) :
    (∫ ω, (Z ω - ∫ ω, Z ω ∂μ) ∂μ) = 0 := by
  rw [integral_sub (hZ.integrable (by norm_num)) (integrable_const _)]
  simp

theorem integral_norm_sq_le_of_bound {n : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hZ : MemLp Z 2 μ) {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ D) :
    (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤ D ^ 2 := by
  calc
    _ ≤ ∫ _ : Ω, D ^ 2 ∂μ := integral_mono_ae
      (hZ.integrable_norm_pow (by norm_num)) (integrable_const _) (by
        filter_upwards [hbound] with ω hω
        exact pow_le_pow_left₀ (norm_nonneg _) hω _)
    _ = _ := by simp

theorem centered_sq_integral_le {n : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hZ : MemLp Z 2 μ) :
    (∫ ω, ‖Z ω - ∫ ω, Z ω ∂μ‖ ^ 2 ∂μ) ≤ ∫ ω, ‖Z ω‖ ^ 2 ∂μ := by
  rw [centered_sq_integral Z hZ]
  exact sub_le_self _ (sq_nonneg _)

theorem identDistrib_centered_sq_integral {n : ℕ}
    (Z Y : Ω → EuclideanSpace ℝ (Fin n)) (h : IdentDistrib Z Y μ μ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, ‖Z ω - x‖ ^ 2 ∂μ) = ∫ ω, ‖Y ω - x‖ ^ 2 ∂μ :=
  (h.comp ((measurable_id.sub_const x).norm.pow_const 2)).integral_eq

/-- The displayed strong law in the empirical-method proof. -/
theorem empirical_strong_law {n : ℕ} (Z : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hZ : MemLp (Z 0) 2 μ) (h_indep : iIndepFun Z μ)
    (h_ident : ∀ j, IdentDistrib (Z j) (Z 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => (k : ℝ)⁻¹ • (∑ j ∈ Finset.range k, Z j ω)) atTop
      (𝓝 (∫ ω, Z 0 ω ∂μ)) :=
  strong_law_ae Z (hZ.integrable (by norm_num))
    (fun _ _ hij => h_indep.indepFun hij) h_ident

/-- Error of a finite empirical average: scaling and independent variance additivity. -/
theorem empirical_mean_sq_integral_eq {n k : ℕ} (hk : 0 < k)
    (Z : Fin k → Ω → EuclideanSpace ℝ (Fin n))
    (hZ : ∀ j, MemLp (Z j) 2 μ) (h_indep : iIndepFun Z μ)
    (x : EuclideanSpace ℝ (Fin n)) (h_mean : ∀ j, ∫ ω, Z j ω ∂μ = x) :
    (∫ ω, ‖x - (k : ℝ)⁻¹ • (∑ j, Z j ω)‖ ^ 2 ∂μ) =
      (k : ℝ)⁻¹ ^ 2 * ∑ j, ∫ ω, ‖Z j ω - x‖ ^ 2 ∂μ := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have heq : ∀ ω, x - (k : ℝ)⁻¹ • (∑ j, Z j ω) =
      -(k : ℝ)⁻¹ • (∑ j, (Z j ω - x)) := by
    intro ω
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul]
    rw [neg_mul, inv_mul_cancel₀ hk0, neg_one_smul]
    simp [neg_smul, sub_eq_add_neg, add_comm]
  simp_rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq]
  rw [integral_const_mul]
  congr 1
  apply independent_mean_zero_sum_sq (fun j ω => Z j ω - x)
  · exact fun j => (hZ j).sub (memLp_const x)
  · exact h_indep.comp (fun _ y => y - x) (fun _ => measurable_id.sub_const x)
  · intro j
    rw [integral_sub ((hZ j).integrable (by norm_num)) (integrable_const _), h_mean j]
    simp

theorem empirical_mean_sq_integral_le {n k : ℕ} (hk : 0 < k)
    (Z : Fin k → Ω → EuclideanSpace ℝ (Fin n))
    (hZ : ∀ j, MemLp (Z j) 2 μ) (h_indep : iIndepFun Z μ)
    (x : EuclideanSpace ℝ (Fin n)) (h_mean : ∀ j, ∫ ω, Z j ω ∂μ = x)
    {D : ℝ} (hbound : ∀ j, (∫ ω, ‖Z j ω‖ ^ 2 ∂μ) ≤ D ^ 2) :
    (∫ ω, ‖x - (k : ℝ)⁻¹ • (∑ j, Z j ω)‖ ^ 2 ∂μ) ≤ D ^ 2 / k := by
  rw [empirical_mean_sq_integral_eq hk Z hZ h_indep x h_mean]
  have hvar : ∀ j, (∫ ω, ‖Z j ω - x‖ ^ 2 ∂μ) ≤ D ^ 2 := by
    intro j
    rw [← h_mean j]
    exact (centered_sq_integral_le (Z j) (hZ j)).trans (hbound j)
  calc
    _ ≤ (k : ℝ)⁻¹ ^ 2 * ∑ _j : Fin k, D ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hvar j) (sq_nonneg _)
    _ = D ^ 2 / k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp

/-- A realization at most the expected squared error exists. -/
theorem exists_realization_le {f : Ω → ℝ} (hf : Integrable f μ) {a : ℝ}
    (ha : (∫ ω, f ω ∂μ) ≤ a) : ∃ ω, f ω ≤ a := by
  obtain ⟨ω, hω⟩ := exists_le_integral hf
  exact ⟨ω, hω.trans ha⟩

theorem exists_realization_mem_le {f : Ω → ℝ} (hf : Integrable f μ) {a : ℝ}
    (ha : (∫ ω, f ω ∂μ) ≤ a) {p : Ω → Prop} (hp : ∀ᵐ ω ∂μ, p ω) :
    ∃ ω, p ω ∧ f ω ≤ a := by
  obtain ⟨ω, hω, hle⟩ := exists_notMem_null_le_integral hf (ae_iff.mp hp)
  exact ⟨ω, by simpa using hω, hle.trans ha⟩

theorem exists_empirical_realization {n k : ℕ} (hk : 0 < k)
    (Z : Fin k → Ω → EuclideanSpace ℝ (Fin n))
    (hZ : ∀ j, MemLp (Z j) 2 μ) (h_indep : iIndepFun Z μ)
    (x : EuclideanSpace ℝ (Fin n)) (h_mean : ∀ j, ∫ ω, Z j ω ∂μ = x)
    {D : ℝ} (hbound : ∀ j, (∫ ω, ‖Z j ω‖ ^ 2 ∂μ) ≤ D ^ 2)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hmem : ∀ j, ∀ᵐ ω ∂μ, Z j ω ∈ T) :
    ∃ ω, (∀ j, Z j ω ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • (∑ j, Z j ω)‖ ^ 2 ≤ D ^ 2 / k := by
  have hsum : MemLp (fun ω => ∑ j, Z j ω) 2 μ :=
    memLp_finset_sum _ (fun j _ => hZ j)
  have herr : MemLp (fun ω => x - (k : ℝ)⁻¹ • (∑ j, Z j ω)) 2 μ :=
    (memLp_const x).sub (hsum.const_smul (k : ℝ)⁻¹)
  exact exists_realization_mem_le (herr.integrable_norm_pow (by norm_num))
    (empirical_mean_sq_integral_le hk Z hZ h_indep x h_mean hbound) (ae_all_iff.mpr hmem)

end HDP

#print axioms HDP.finiteIndexLaw_singleton
#print axioms HDP.finiteIndexLaw_value_probability
#print axioms HDP.finiteIndexLaw_expectation
#print axioms HDP.finiteIndexLaw_memLp
#print axioms HDP.exists_finite_law_independent_copies
#print axioms HDP.exists_independent_copies
#print axioms HDP.integral_centered_eq_zero
#print axioms HDP.integral_norm_sq_le_of_bound
#print axioms HDP.centered_sq_integral_le
#print axioms HDP.identDistrib_centered_sq_integral
#print axioms HDP.empirical_strong_law
#print axioms HDP.empirical_mean_sq_integral_eq
#print axioms HDP.empirical_mean_sq_integral_le
#print axioms HDP.exists_realization_le
#print axioms HDP.exists_realization_mem_le
#print axioms HDP.exists_empirical_realization
