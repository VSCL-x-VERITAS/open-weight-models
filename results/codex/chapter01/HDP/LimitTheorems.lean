import HDP.PoissonLimit

/-! Probability limits and finite-sample estimates for Chapter 1.
The finite-variance iid CLT is proved by characteristic-function expansion,
uniform second-moment tightness and Prokhorov compactness. Positive variance
is the explicit correction needed for the source's Gaussian normalization.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology BigOperators NNReal

namespace HDP.Limits

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Source index 1 is Lean index 0. -/
noncomputable def sampleSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, X i ω

noncomputable def sampleMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sampleSum X n ω / (n : ℝ)

/-- Full independence and identical distribution, as in the source. -/
def IID (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  iIndepFun X P ∧ ∀ i, IdentDistrib (X i) (X 0) P P

noncomputable def normalizedSum (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (sampleSum X n ω - (n : ℝ) * ∫ ω, X 0 ω ∂P) /
    Real.sqrt ((n : ℝ) * variance (X 0) P)

noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

noncomputable def weightedCharacteristic (P : Measure Ω) (H : Ω → ℂ) (Y : Ω → ℝ)
    (t : ℝ) : ℂ :=
  ∫ ω, H ω * Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) ∂P

lemma IID.memLp (h : IID P X) (hX : MemLp (X 0) 2 P) (i : ℕ) :
    MemLp (X i) 2 P :=
  (h.2 i).symm.memLp_snd hX

lemma IID.integrable (h : IID P X) (hX : Integrable (X 0) P) (i : ℕ) :
    Integrable (X i) P :=
  (h.2 i).symm.integrable_snd hX

lemma sampleSum_memLp (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) (n : ℕ) :
    MemLp (sampleSum X n) 2 P := by
  simpa [sampleSum] using memLp_finset_sum (range n) (fun i _ => hX i)

lemma sampleMean_memLp (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) (n : ℕ) :
    MemLp (sampleMean X n) 2 P := by
  change MemLp (fun ω => sampleSum X n ω / (n : ℝ)) 2 P
  simpa only [div_eq_mul_inv, mul_comm] using
    (sampleSum_memLp X hX n).const_mul ((n : ℝ)⁻¹)

lemma integral_sampleSum (X : ℕ → Ω → ℝ) (hX : ∀ i, Integrable (X i) P) (n : ℕ) :
    (∫ ω, sampleSum X n ω ∂P) = ∑ i ∈ range n, ∫ ω, X i ω ∂P := by
  exact integral_finset_sum _ (fun i _ => hX i)

lemma iid_integral_sampleSum (h : IID P X) (hX : Integrable (X 0) P) (n : ℕ) :
    (∫ ω, sampleSum X n ω ∂P) = (n : ℝ) * ∫ ω, X 0 ω ∂P := by
  rw [integral_sampleSum X (h.integrable hX)]
  simp_rw [(h.2 _).integral_eq]
  simp

/-- Reusable setwise variance additivity; finite source wrappers follow below. -/
theorem variance_independent_sum {ι : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (hindep : Set.Pairwise (↑s) (fun i j => IndepFun (X i) (X j) P))
    (hX : ∀ i ∈ s, MemLp (X i) 2 P) :
    variance (fun ω => ∑ i ∈ s, X i ω) P = ∑ i ∈ s, variance (X i) P := by
  have heq : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    ext ω
    simp
  rw [heq]
  exact IndepFun.variance_sum hX hindep

/-- Variance additivity for a finite family; no infinite extension is assumed. -/
theorem finite_variance_sum {n : ℕ} (X : Fin n → Ω → ℝ)
    (hindep : iIndepFun X P) (hX : ∀ i, MemLp (X i) 2 P) :
    variance (fun ω => ∑ i, X i ω) P = ∑ i, variance (X i) P :=
  variance_independent_sum X univ (fun i _ j _ hij => hindep.indepFun hij) (fun i _ => hX i)

/-- The finite-sample identity (1.5) using precisely finite independence and moments. -/
theorem finite_variance_sampleMean {n : ℕ} (X : Fin n → Ω → ℝ)
    (hindep : iIndepFun X P) (hX : ∀ i, MemLp (X i) 2 P)
    (μ v : ℝ) (_hmean : ∀ i, (∫ ω, X i ω ∂P) = μ)
    (hvar : ∀ i, variance (X i) P = v) (hn : 0 < n) :
    variance (fun ω => (∑ i, X i ω) / (n : ℝ)) P = v / (n : ℝ) := by
  simp_rw [div_eq_mul_inv, mul_comm _ ((n : ℝ)⁻¹)]
  rw [variance_const_mul, finite_variance_sum X hindep hX]
  simp_rw [hvar]
  simp only [sum_const, card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

lemma iid_variance_sampleSum (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) :
    variance (sampleSum X n) P = (n : ℝ) * variance (X 0) P := by
  change variance (fun ω => ∑ i ∈ range n, X i ω) P = _
  rw [variance_independent_sum X (range n) (fun i _ j _ hij => h.1.indepFun hij)
    (fun i _ => h.memLp hX i)]
  simp_rw [(h.2 _).variance_eq]
  simp

/-- Equation (1.5). The identity also has the correct totalized value at n=0. -/
theorem iid_variance_sampleMean (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) :
    variance (sampleMean X n) P = variance (X 0) P / (n : ℝ) := by
  unfold sampleMean
  simp_rw [div_eq_mul_inv, mul_comm _ ((n : ℝ)⁻¹)]
  rw [variance_const_mul, iid_variance_sampleSum h hX]
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp

theorem iid_variance_sampleMean_tendsto_zero (h : IID P X)
    (hX : MemLp (X 0) 2 P) :
    Tendsto (fun n => variance (sampleMean X n) P) atTop (𝓝 0) := by
  simp_rw [iid_variance_sampleMean h hX]
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

section ProbabilitySpace

variable [IsProbabilityMeasure P]

/-- Theorem 1.3.1, with finite expectation made explicit by integrability. -/
theorem strong_law (h : IID P X) (hX : Integrable (X 0) P) {μ : ℝ}
    (hmean : (∫ ω, X 0 ω ∂P) = μ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleMean X n ω) atTop (𝓝 μ) := by
  simpa only [sampleMean, sampleSum, hmean] using
    strong_law_ae_real X hX (fun i j hij => h.1.indepFun hij) h.2

lemma iid_integral_sampleMean (h : IID P X) (hX : Integrable (X 0) P)
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, sampleMean X n ω ∂P) = ∫ ω, X 0 ω ∂P := by
  change (∫ ω, sampleSum X n ω / (n : ℝ) ∂P) = _
  rw [integral_div, iid_integral_sampleSum h hX]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- IID characteristic-function factorization: the first reduction in a CLT proof. -/
lemma iid_charFun_sampleSum (h : IID P X) (n : ℕ) (t : ℝ) :
    charFun (P.map (sampleSum X n)) t = (charFun (P.map (X 0)) t) ^ n := by
  let Y : Fin n → Ω → ℝ := fun i => X i.val
  have hi : iIndepFun Y P := h.1.precomp Fin.val_injective
  have hm : ∀ i, AEMeasurable (Y i) P := fun i => (h.2 i.val).aemeasurable_fst
  have heq : sampleSum X n = ∑ i, Y i := by
    ext ω
    simpa only [sampleSum, Y, Finset.sum_apply] using
      (Fin.sum_univ_eq_sum_range (fun i => X i ω) n).symm
  calc
    charFun (P.map (sampleSum X n)) t = ∏ i : Fin n, charFun (P.map (Y i)) t := by
      rw [heq]
      simpa only [Finset.prod_apply] using congrFun (hi.charFun_map_sum_eq_prod hm) t
    _ = (charFun (P.map (X 0)) t) ^ n := by
      simp_rw [Y, (h.2 _).map_eq]
      simp

set_option backward.isDefEq.respectTransparency false in
lemma charFun_map_eq_weightedCharacteristic {Y : Ω → ℝ} (hY : AEMeasurable Y P) (t : ℝ) :
    charFun (P.map Y) t = weightedCharacteristic P (fun _ => 1) Y t := by
  rw [charFun_apply_real, integral_map hY]
  · simp only [weightedCharacteristic, one_mul, Function.comp_apply, Complex.ofReal_mul,
      mul_comm (t : ℂ)]
  · fun_prop

/-- Cauchy–Schwarz against the constant function, proved using nonnegative variance. -/
lemma integral_abs_le_sqrt_integral_sq {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    (∫ ω, |Y ω| ∂P) ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := by
  apply Real.le_sqrt_of_sq_le
  have hv := variance_nonneg (fun ω => |Y ω|) P
  have ha : MemLp (fun ω => |Y ω|) 2 P := by
    simpa only [Real.norm_eq_abs] using hY.norm
  rw [variance_eq_sub ha] at hv
  simpa only [Pi.pow_apply, sq_abs] using (sub_nonneg.mp hv)

/-- Explicit bound underlying Exercise 1.3.3. -/
theorem iid_integral_abs_sampleMean_sub_le (h : IID P X) (hX : MemLp (X 0) 2 P)
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, |sampleMean X n ω - ∫ ω, X 0 ω ∂P| ∂P) ≤
      Real.sqrt (variance (X 0) P) / Real.sqrt (n : ℝ) := by
  have hm := sampleMean_memLp X (h.memLp hX) n
  have hmean := iid_integral_sampleMean h (hX.integrable (by norm_num)) hn
  have hv : (∫ ω, (sampleMean X n ω - ∫ ω, X 0 ω ∂P) ^ 2 ∂P) =
      variance (sampleMean X n) P := by
    rw [variance_eq_integral hm.aemeasurable, hmean]
  calc
    (∫ ω, |sampleMean X n ω - ∫ ω, X 0 ω ∂P| ∂P) ≤
        Real.sqrt (∫ ω, (sampleMean X n ω - ∫ ω, X 0 ω ∂P) ^ 2 ∂P) :=
      integral_abs_le_sqrt_integral_sq (hm.sub (memLp_const _))
    _ = Real.sqrt (variance (X 0) P) / Real.sqrt (n : ℝ) := by
      rw [hv, iid_variance_sampleMean h hX, Real.sqrt_div (variance_nonneg _ _)]

theorem iid_absolute_mean_rate (h : IID P X) (hX : MemLp (X 0) 2 P) :
    (fun n => ∫ ω, |sampleMean X n ω - ∫ ω, X 0 ω ∂P| ∂P) =O[atTop]
      (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨Real.sqrt (variance (X 0) P), ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _)),
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ)), mul_one_div] using
    iid_integral_abs_sampleMean_sub_le h hX hn

/-- The two normalizations displayed before Theorem 1.3.2 agree. -/
theorem normalizedSum_eq_centered (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) :
    normalizedSum P X n = (fun ω =>
      (∑ i ∈ range n, (X i ω - ∫ ω, X 0 ω ∂P)) /
        (Real.sqrt (variance (X 0) P) * Real.sqrt (n : ℝ))) := by
  funext ω
  simp only [normalizedSum, sampleSum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg n), mul_comm (Real.sqrt (n : ℝ))]

theorem normalizedSum_eq_variance_normalization (h : IID P X)
    (hX : MemLp (X 0) 2 P) (n : ℕ) :
    normalizedSum P X n = (fun ω =>
      (sampleSum X n ω - ∫ ω, sampleSum X n ω ∂P) /
        Real.sqrt (variance (sampleSum X n) P)) := by
  funext ω
  simp only [normalizedSum, iid_integral_sampleSum h (hX.integrable (by norm_num)),
    iid_variance_sampleSum h hX]

/-- Zero mean of the normalized variable. -/
theorem integral_normalizedSum (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) :
    (∫ ω, normalizedSum P X n ω ∂P) = 0 := by
  unfold normalizedSum
  rw [integral_div, integral_sub ((sampleSum_memLp X (h.memLp hX) n).integrable (by norm_num))
    (integrable_const _)]
  rw [iid_integral_sampleSum h (hX.integrable (by norm_num))]
  simp

/-- Unit variance requires the explicit correction of positive source variance. -/
theorem variance_normalizedSum (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) {n : ℕ} (hn : 0 < n) :
    variance (normalizedSum P X n) P = 1 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < (n : ℝ) * variance (X 0) P := mul_pos hn' hv
  unfold normalizedSum
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, variance_sub_const (sampleSum_memLp X (h.memLp hX) n).1,
    iid_variance_sampleSum h hX, inv_pow, Real.sq_sqrt hd.le]
  exact mul_inv_cancel₀ hd.ne'

lemma normalizedSum_memLp (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) :
    MemLp (normalizedSum P X n) 2 P := by
  unfold normalizedSum
  simpa only [div_eq_mul_inv] using
    ((sampleSum_memLp X (h.memLp hX) n).sub (memLp_const _)).mul_const
      ((Real.sqrt ((n : ℝ) * variance (X 0) P))⁻¹)

/-- Uniform normalized second-moment control, supplying CLT tightness. -/
lemma normalizedSum_tail_le (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ |normalizedSum P X n ω|} ≤ ENNReal.ofReal (1 / t ^ 2) := by
  by_cases hn : n = 0
  · subst n
    simp [normalizedSum, sampleSum, not_le.mpr ht]
  · have hb := meas_ge_le_variance_div_sq (normalizedSum_memLp h hX n) ht
    simpa only [integral_normalizedSum h hX n, sub_zero,
      variance_normalizedSum h hX hv (Nat.pos_of_ne_zero hn)] using hb

/-- Tightness of all normalized iid-sum laws follows from their uniform second moments. -/
theorem isTight_normalizedSum (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) :
    IsTightMeasureSet (Set.range (fun n => P.map (normalizedSum P X n))) := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  have hr : Tendsto (fun r : ℝ => 1 / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have he : Tendsto (fun r : ℝ => ENNReal.ofReal (1 / r ^ 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hrpos
  refine iSup_le (fun μ => iSup_le (fun hμ => ?_))
  obtain ⟨n, rfl⟩ := hμ
  rw [Measure.map_apply_of_aemeasurable (normalizedSum_memLp h hX n).aemeasurable
    (measurableSet_lt measurable_const measurable_norm)]
  refine le_trans (measure_mono ?_) (normalizedSum_tail_le h hX hv n hrpos)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.norm_eq_abs] at hω ⊢
  exact le_of_lt hω

/-- The standard normal density is the Gaussian density (1.6). -/
theorem standardNormalDensity_eq_gaussianPDF (x : ℝ) :
    standardNormalDensity x = gaussianPDFReal 0 1 x := by
  simp [standardNormalDensity, gaussianPDFReal]

/-- The normal tail appearing after Theorem 1.3.2 has the stated density integral. -/
theorem standardNormal_tail_integral (t : ℝ) :
    (gaussianReal 0 1).real (Set.Ici t) =
      ∫ x in Set.Ici t, standardNormalDensity x := by
  simp_rw [standardNormalDensity_eq_gaussianPDF]
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))

end ProbabilitySpace

lemma continuous_weightedCharacteristic {Y : Ω → ℝ} {H : Ω → ℂ}
    (hY : AEMeasurable Y P) (hH : Integrable H P) :
    Continuous (weightedCharacteristic P H Y) := by
  apply continuous_of_dominated (bound := fun ω => ‖H ω‖)
  · intro t
    fun_prop
  · intro t
    filter_upwards with ω
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  · exact hH.norm
  · filter_upwards with ω
    fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation of a weighted characteristic integral under a first-moment bound. -/
lemma hasDerivAt_weighted_characteristic {Y : Ω → ℝ} {H : Ω → ℂ}
    (hY : AEMeasurable Y P) (hH : Integrable H P)
    (hHY : Integrable (fun ω => H ω * (Y ω : ℂ) * Complex.I) P) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ ω, H ω * Complex.exp (((s * Y ω : ℝ) : ℂ) * Complex.I) ∂P)
      (∫ ω, H ω * (Y ω : ℂ) * Complex.I *
        Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) ∂P) t := by
  let F : ℝ → Ω → ℂ := fun s ω =>
    H ω * Complex.exp (((s * Y ω : ℝ) : ℂ) * Complex.I)
  let F' : ℝ → Ω → ℂ := fun s ω =>
    H ω * (Y ω : ℂ) * Complex.I * Complex.exp (((s * Y ω : ℝ) : ℂ) * Complex.I)
  have hm (s : ℝ) : AEStronglyMeasurable (F s) P := by
    dsimp [F]
    fun_prop
  have hm' : AEStronglyMeasurable (F' t) P := by
    dsimp [F']
    fun_prop
  have hi : Integrable (F t) P := by
    apply hH.norm.mono' (hm t)
    filter_upwards with ω
    dsimp only [F]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hb : ∀ᵐ ω ∂P, ∀ s ∈ (Set.univ : Set ℝ),
      ‖F' s ω‖ ≤ ‖H ω * (Y ω : ℂ) * Complex.I‖ := by
    filter_upwards with ω s _
    dsimp only [F']
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hd : ∀ᵐ ω ∂P, ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun a => F a ω) (F' s ω) s := by
    filter_upwards with ω s _
    convert ((((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (Y ω : ℂ)).mul_const
      Complex.I).cexp.const_mul (H ω)) using 1 <;>
      simp [F, F', Complex.ofRealCLM_apply, Complex.ofReal_mul,
        mul_assoc, mul_comm, mul_left_comm]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (bound := fun ω => ‖H ω * (Y ω : ℂ) * Complex.I‖) (Filter.univ_mem)
    (Filter.Eventually.of_forall hm) hi hm' hb hHY.norm hd).2

lemma contDiff_one_weightedCharacteristic {Y : Ω → ℝ} {H : Ω → ℂ}
    (hY : AEMeasurable Y P) (hH : Integrable H P)
    (hHY : Integrable (fun ω => H ω * (Y ω : ℂ) * Complex.I) P) :
    ContDiff ℝ 1 (weightedCharacteristic P H Y) := by
  have hd (t : ℝ) : HasDerivAt (weightedCharacteristic P H Y)
      (weightedCharacteristic P (fun ω => H ω * (Y ω : ℂ) * Complex.I) Y t) t :=
    hasDerivAt_weighted_characteristic hY hH hHY t
  have heq : deriv (weightedCharacteristic P H Y) =
      weightedCharacteristic P (fun ω => H ω * (Y ω : ℂ) * Complex.I) Y :=
    funext (fun t => (hd t).deriv)
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  rw [heq]
  exact continuous_weightedCharacteristic hY hHY

lemma contDiff_two_characteristic [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) :
    ContDiff ℝ 2 (weightedCharacteristic P (fun _ => 1) Y) := by
  have hymeas : AEMeasurable Y P := hY.aemeasurable
  have hi : Integrable (fun ω => (Y ω : ℂ) * Complex.I) P :=
    (hY.integrable (by norm_num)).ofReal.mul_const _
  have hi' : Integrable (fun ω => ((Y ω : ℂ) * Complex.I) * (Y ω : ℂ) * Complex.I) P := by
    apply hY.integrable_sq.mono' (by fun_prop)
    filter_upwards with ω
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_abs (Y ω)]
  have hd (t : ℝ) : HasDerivAt (weightedCharacteristic P (fun _ => 1) Y)
      (weightedCharacteristic P (fun ω => (Y ω : ℂ) * Complex.I) Y t) t := by
    unfold weightedCharacteristic
    simpa only [one_mul] using
      hasDerivAt_weighted_characteristic hY.aemeasurable (integrable_const 1)
        (by simpa only [one_mul] using hi) t
  have heq : deriv (weightedCharacteristic P (fun _ => 1) Y) =
      weightedCharacteristic P (fun ω => (Y ω : ℂ) * Complex.I) Y :=
    funext (fun t => (hd t).deriv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, by norm_num, ?_⟩
  rw [heq]
  exact contDiff_one_weightedCharacteristic hY.aemeasurable hi hi'

/-- Taylor–Peano remainder for characteristic functions with finite second moment. -/
lemma characteristic_taylor_remainder [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) :
    (fun t => weightedCharacteristic P (fun _ => 1) Y t -
      taylorWithinEval (weightedCharacteristic P (fun _ => 1) Y) 2 Set.univ 0 t)
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  simpa only [nhdsWithin_univ, sub_zero] using
    (taylor_isLittleO convex_univ (Set.mem_univ (0 : ℝ))
      (contDiff_two_characteristic hY).contDiffOn)

set_option backward.isDefEq.respectTransparency false in
/-- First two Taylor coefficients at zero, under the standard normalization. -/
lemma characteristic_standard_taylor_coefficients [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) (hmean : (∫ ω, Y ω ∂P) = 0) (hvar : variance Y P = 1) :
    let φ := weightedCharacteristic P (fun _ => 1) Y
    φ 0 = 1 ∧ deriv φ 0 = 0 ∧ iteratedDeriv 2 φ 0 = -1 := by
  dsimp only
  have hymeas : AEMeasurable Y P := hY.aemeasurable
  have hi : Integrable (fun ω => (Y ω : ℂ) * Complex.I) P :=
    (hY.integrable (by norm_num)).ofReal.mul_const _
  have hi' : Integrable (fun ω => ((Y ω : ℂ) * Complex.I) * (Y ω : ℂ) * Complex.I) P := by
    apply hY.integrable_sq.mono' (by fun_prop)
    filter_upwards with ω
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_abs (Y ω)]
  have hd (t : ℝ) : HasDerivAt (weightedCharacteristic P (fun _ => 1) Y)
      (weightedCharacteristic P (fun ω => (Y ω : ℂ) * Complex.I) Y t) t := by
    unfold weightedCharacteristic
    simpa only [one_mul] using
      hasDerivAt_weighted_characteristic hymeas (integrable_const 1)
        (by simpa only [one_mul] using hi) t
  have heq : deriv (weightedCharacteristic P (fun _ => 1) Y) =
      weightedCharacteristic P (fun ω => (Y ω : ℂ) * Complex.I) Y :=
    funext (fun t => (hd t).deriv)
  have he2 : (fun ω => (Y ω : ℂ) * Complex.I * (Y ω : ℂ) * Complex.I) =
      (fun ω => -((Y ω ^ 2 : ℝ) : ℂ)) := by
    funext ω
    push_cast
    calc
      (Y ω : ℂ) * Complex.I * (Y ω : ℂ) * Complex.I =
          (Y ω : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = -(Y ω : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
  have hsq : (∫ ω, Y ω ^ 2 ∂P) = 1 := by
    rw [← variance_of_integral_eq_zero hymeas hmean, hvar]
  refine ⟨by simp [weightedCharacteristic], ?_, ?_⟩
  · rw [heq]
    simp only [weightedCharacteristic, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one]
    rw [integral_mul_const, integral_complex_ofReal, hmean]
    simp
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, heq]
    unfold weightedCharacteristic
    rw [(hasDerivAt_weighted_characteristic hymeas hi hi' 0).deriv]
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    rw [he2, integral_neg, integral_complex_ofReal, hsq]
    norm_num

set_option backward.isDefEq.respectTransparency false in
/-- The standard finite-second-moment expansion, with a genuine little-o remainder. -/
lemma characteristic_standard_taylor [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) (hmean : (∫ ω, Y ω ∂P) = 0) (hvar : variance Y P = 1) :
    (fun t : ℝ => weightedCharacteristic P (fun _ => 1) Y t -
      (1 - (t : ℂ) ^ 2 / 2)) =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  let φ := weightedCharacteristic P (fun _ => 1) Y
  obtain ⟨h0, h1, h2⟩ := characteristic_standard_taylor_coefficients hY hmean hvar
  have hp (t : ℝ) : taylorWithinEval φ 2 Set.univ 0 t = 1 - (t : ℂ) ^ 2 / 2 := by
    norm_num [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
      iteratedDeriv_zero, iteratedDeriv_one, h0, h1, h2, φ, Complex.real_smul]
    <;> push_cast <;> ring
  have hr : (fun t => φ t - taylorWithinEval φ 2 Set.univ 0 t) =o[𝓝 0]
      (fun t : ℝ => t ^ 2) := characteristic_taylor_remainder hY
  simpa only [hp] using hr

set_option backward.isDefEq.respectTransparency false in
/-- The analytic power limit used in the iid central limit theorem. -/
lemma scaled_taylor_power_limit (φ : ℝ → ℂ) (hφ0 : φ 0 = 1)
    (hφ : (fun s : ℝ => φ s - (1 - (s : ℂ) ^ 2 / 2)) =o[𝓝 0]
      (fun s : ℝ => s ^ 2)) (t : ℝ) :
    Tendsto (fun n : ℕ => (φ (t / Real.sqrt (n : ℝ))) ^ n) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  by_cases ht : t = 0
  · subst t
    simpa only [zero_div, hφ0, one_pow, Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, neg_zero, Complex.exp_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  have hs : Tendsto (fun n : ℕ => t / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hr := (hφ.tendsto_inv_smul_nhds_zero (𝕜 := ℝ)).comp hs
  have hr' := (hr.const_smul (t ^ 2)).sub_const ((t : ℂ) ^ 2 / 2)
  have hc : Tendsto (fun n : ℕ => (n : ℂ) * (φ (t / Real.sqrt (n : ℝ)) - 1)) atTop
      (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
    simp only [smul_zero, zero_sub] at hr'
    rw [neg_div]
    apply hr'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have ht' : t ^ 2 ≠ 0 := pow_ne_zero _ ht
    have heq : t ^ 2 * ((t / Real.sqrt (n : ℝ)) ^ 2)⁻¹ = (n : ℝ) := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp
    have hns : (n : ℝ) * (t / Real.sqrt (n : ℝ)) ^ 2 = t ^ 2 := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp
    have hnsC : (n : ℂ) * ((t / Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
      exact_mod_cast hns
    dsimp only [Function.comp_def]
    rw [← mul_smul, heq]
    simp only [Complex.real_smul, Complex.ofReal_natCast]
    linear_combination hnsC / 2
  have hp := Complex.tendsto_one_add_pow_exp_of_tendsto hc
  simpa only [add_sub_cancel] using hp

/-- Characteristic functions are continuous in the weak topology on probability laws. -/
lemma continuous_charFun_probability (t : ℝ) :
    Continuous (fun ν : ProbabilityMeasure ℝ => charFun (ν : Measure ℝ) t) := by
  rw [continuous_iff_continuousAt]
  intro ν
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (continuous_id.continuousAt (x := ν)) (BoundedContinuousFunction.innerProbChar t)
  simpa only [charFun_eq_integral_innerProbChar] using h

/-- A tight family with convergent characteristic functions converges weakly.
This compactness criterion is a reusable prerequisite, not the missing CLT itself. -/
theorem tendsto_probability_of_tight_charFun (u : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ)
    (htight : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range u})
    (hchar : ∀ t : ℝ, Tendsto (fun n => charFun (u n : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t))) :
    Tendsto u atTop (𝓝 ν) := by
  apply (isCompact_closure_of_isTightMeasureSet htight).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall (fun n => subset_closure (Set.mem_range_self n)))
  intro ρ _ hρ
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have hc := hρ.continuousAt_comp (continuous_charFun_probability t).continuousAt
  let L := 𝓝 (charFun (ρ : Measure ℝ) t) ⊓
    Filter.map (fun n => charFun (u n : Measure ℝ) t) atTop
  haveI : NeBot L := hc
  have h₁ : Tendsto id L (𝓝 (charFun (ρ : Measure ℝ) t)) := by
    simpa only [Filter.Tendsto, Filter.map_id] using
      (inf_le_left : L ≤ 𝓝 (charFun (ρ : Measure ℝ) t))
  have h₂ : Tendsto id L (𝓝 (charFun (ν : Measure ℝ) t)) := by
    simpa only [Filter.Tendsto, Filter.map_id] using
      (inf_le_right.trans (hchar t) : L ≤ 𝓝 (charFun (ν : Measure ℝ) t))
  exact tendsto_nhds_unique h₁ h₂

/-- Weak convergence to an atomless law gives the source's pointwise CDF conclusion. -/
theorem cdf_tendsto_of_weak {u : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    [NoAtoms (ν : Measure ℝ)] (h : Tendsto u atTop (𝓝 ν)) (t : ℝ) :
    Tendsto (fun n => (u n : Measure ℝ).real (Set.Iic t)) atTop
      (𝓝 ((ν : Measure ℝ).real (Set.Iic t))) := by
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h
    (E := Set.Iic t) (by simp only [frontier_Iic, measure_singleton])
  exact (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) _)).comp hp

/-- The closed upper-tail conclusion uses the same null-boundary criterion. -/
theorem closedTail_tendsto_of_weak {u : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    [NoAtoms (ν : Measure ℝ)] (h : Tendsto u atTop (𝓝 ν)) (t : ℝ) :
    Tendsto (fun n => (u n : Measure ℝ).real (Set.Ici t)) atTop
      (𝓝 ((ν : Measure ℝ).real (Set.Ici t))) := by
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h
    (E := Set.Ici t) (by simp only [frontier_Ici, measure_singleton])
  exact (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) _)).comp hp

section CLT

variable [IsProbabilityMeasure P]

noncomputable def standardizedVariable (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (i : ℕ) (ω : Ω) : ℝ :=
  (X i ω - ∫ ω, X 0 ω ∂P) / Real.sqrt (variance (X 0) P)

lemma iid_standardizedVariable (h : IID P X) : IID P (standardizedVariable P X) := by
  refine ⟨?_, ?_⟩
  · exact h.1.comp (fun _ x => (x - ∫ ω, X 0 ω ∂P) / Real.sqrt (variance (X 0) P))
      (fun _ => by fun_prop)
  · intro i
    exact ((h.2 i).sub_const _).div_const _

lemma standardizedVariable_zero_eq (X : ℕ → Ω → ℝ) :
    standardizedVariable P X 0 = normalizedSum P X 1 := by
  funext ω
  simp [standardizedVariable, normalizedSum, sampleSum]

lemma normalizedSum_eq_standardizedSum (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) :
    normalizedSum P X n =
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ * sampleSum (standardizedVariable P X) n ω) := by
  rw [normalizedSum_eq_centered h hX n]
  funext ω
  simp only [sampleSum, standardizedVariable, ← Finset.sum_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma iid_charFun_normalizedSum (h : IID P X) (hX : MemLp (X 0) 2 P) (n : ℕ) (t : ℝ) :
    charFun (P.map (normalizedSum P X n)) t =
      (weightedCharacteristic P (fun _ => 1) (standardizedVariable P X 0)
        (t / Real.sqrt (n : ℝ))) ^ n := by
  let Y := standardizedVariable P X
  have hyiid : IID P Y := iid_standardizedVariable h
  have hylp : MemLp (Y 0) 2 P := by
    rw [show Y 0 = normalizedSum P X 1 from standardizedVariable_zero_eq X]
    exact normalizedSum_memLp h hX 1
  have hsm := (sampleSum_memLp Y (hyiid.memLp hylp) n).aemeasurable
  have heq : P.map (normalizedSum P X n) =
      (P.map (sampleSum Y n)).map (fun x => (Real.sqrt (n : ℝ))⁻¹ * x) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hsm]
    congr 1
    exact normalizedSum_eq_standardizedSum h hX n
  rw [heq, charFun_map_mul, iid_charFun_sampleSum hyiid]
  rw [charFun_map_eq_weightedCharacteristic hylp.aemeasurable]
  simp only [div_eq_mul_inv, mul_comm t]
  rfl

/-- The characteristic-function core of the finite-variance iid central limit theorem. -/
theorem normalizedSum_charFun_tendsto (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) (t : ℝ) :
    Tendsto (fun n => charFun (P.map (normalizedSum P X n)) t) atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hy : MemLp (standardizedVariable P X 0) 2 P := by
    rw [standardizedVariable_zero_eq X]
    exact normalizedSum_memLp h hX 1
  have hm : (∫ ω, standardizedVariable P X 0 ω ∂P) = 0 := by
    rw [standardizedVariable_zero_eq X]
    exact integral_normalizedSum h hX 1
  have hv' : variance (standardizedVariable P X 0) P = 1 := by
    rw [standardizedVariable_zero_eq X]
    exact variance_normalizedSum h hX hv (by norm_num)
  have h0 := (characteristic_standard_taylor_coefficients hy hm hv').1
  have hp := scaled_taylor_power_limit _ h0 (characteristic_standard_taylor hy hm hv') t
  simpa only [iid_charFun_normalizedSum h hX] using hp

noncomputable def normalizedLaw (h : IID P X) (hX : MemLp (X 0) 2 P)
    (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨P.map (normalizedSum P X n), P.isProbabilityMeasure_map
    (normalizedSum_memLp h hX n).aemeasurable⟩

noncomputable def standardNormalLaw : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- Theorem 1.3.2: weak convergence of the normalized sum laws to standard Gaussian.
Positive variance is the explicit correction needed for the source normalization. -/
theorem central_limit_weak (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) :
    Tendsto (normalizedLaw h hX) atTop (𝓝 standardNormalLaw) := by
  apply tendsto_probability_of_tight_charFun
  · have hs : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range (normalizedLaw h hX)} =
        Set.range (fun n => P.map (normalizedSum P X n)) := by
      ext μ
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨normalizedLaw h hX n, ⟨n, rfl⟩, rfl⟩
    rw [hs]
    exact isTight_normalizedSum h hX hv
  · intro t
    change Tendsto (fun n => charFun (P.map (normalizedSum P X n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t))
    simpa only [charFun_gaussianReal, NNReal.coe_one, Complex.ofReal_zero, Complex.ofReal_one,
      mul_zero, zero_mul, one_mul, zero_sub, neg_div] using
      normalizedSum_charFun_tendsto h hX hv t

/-- The pointwise CDF conclusion printed immediately after Theorem 1.3.2. -/
theorem central_limit_cdf (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) (t : ℝ) :
    Tendsto (fun n => P.real {ω | normalizedSum P X n ω ≤ t}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  letI : NoAtoms (standardNormalLaw : Measure ℝ) := noAtoms_gaussianReal (by norm_num)
  have hp := cdf_tendsto_of_weak (central_limit_weak h hX hv) t
  change Tendsto (fun n => (P.map (normalizedSum P X n)).real (Set.Iic t)) atTop _ at hp
  simp only [Measure.real, Measure.map_apply_of_aemeasurable
    (normalizedSum_memLp h hX _).aemeasurable measurableSet_Iic] at hp
  exact hp

/-- The closed-tail formulation displayed in Theorem 1.3.2. -/
theorem central_limit_closedTail (h : IID P X) (hX : MemLp (X 0) 2 P)
    (hv : 0 < variance (X 0) P) (t : ℝ) :
    Tendsto (fun n => P.real {ω | t ≤ normalizedSum P X n ω}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Ici t))) := by
  letI : NoAtoms (standardNormalLaw : Measure ℝ) := noAtoms_gaussianReal (by norm_num)
  have hp := closedTail_tendsto_of_weak (central_limit_weak h hX hv) t
  change Tendsto (fun n => (P.map (normalizedSum P X n)).real (Set.Ici t)) atTop _ at hp
  simp only [Measure.real, Measure.map_apply_of_aemeasurable
    (normalizedSum_memLp h hX _).aemeasurable measurableSet_Ici] at hp
  exact hp

/-- Equation (1.7), the de Moivre–Laplace theorem, in the source's CDF characterization
of convergence in distribution. Independence and the common Bernoulli law imply iid. -/
theorem deMoivre_laplace_cdf (X : ℕ → Ω → ℝ) (p : ℝ≥0) (hp0 : 0 < p)
    (hp1 : p < 1) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (HDP.bernoulliMeasure p hp1.le) P) (t : ℝ) :
    Tendsto (fun n => P.real {ω |
      (sampleSum X n ω - (n : ℝ) * (p : ℝ)) /
        Real.sqrt ((n : ℝ) * (p : ℝ) * (1 - (p : ℝ))) ≤ t}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  have h : IID P X := ⟨hindep, fun i => (hlaw i).identDistrib (hlaw 0)⟩
  have hm := HDP.hasLaw_bernoulli_expectation p hp1.le (hlaw 0)
  have hvar := HDP.hasLaw_bernoulli_variance p hp1.le (hlaw 0)
  have hv : 0 < variance (X 0) P := by
    rw [hvar]
    exact mul_pos (by exact_mod_cast hp0) (sub_pos.mpr (by exact_mod_cast hp1))
  simpa only [normalizedSum, hm, hvar, ← mul_assoc] using
    central_limit_cdf h (HDP.hasLaw_bernoulli_memLp p hp1.le (hlaw 0)) hv t

theorem deMoivre_laplace_closedTail (X : ℕ → Ω → ℝ) (p : ℝ≥0) (hp0 : 0 < p)
    (hp1 : p < 1) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (HDP.bernoulliMeasure p hp1.le) P) (t : ℝ) :
    Tendsto (fun n => P.real {ω | t ≤
      (sampleSum X n ω - (n : ℝ) * (p : ℝ)) /
        Real.sqrt ((n : ℝ) * (p : ℝ) * (1 - (p : ℝ)))}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Ici t))) := by
  have h : IID P X := ⟨hindep, fun i => (hlaw i).identDistrib (hlaw 0)⟩
  have hm := HDP.hasLaw_bernoulli_expectation p hp1.le (hlaw 0)
  have hvar := HDP.hasLaw_bernoulli_variance p hp1.le (hlaw 0)
  have hv : 0 < variance (X 0) P := by
    rw [hvar]
    exact mul_pos (by exact_mod_cast hp0) (sub_pos.mpr (by exact_mod_cast hp1))
  simpa only [normalizedSum, hm, hvar, ← mul_assoc] using
    central_limit_closedTail h (HDP.hasLaw_bernoulli_memLp p hp1.le (hlaw 0)) hv t

end CLT

end HDP.Limits
