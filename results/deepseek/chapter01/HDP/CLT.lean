/-
The Lindeberg--Lévy central limit theorem for i.i.d. real random variables with
finite second moment, proved via characteristic functions, tightness and the
characteristic-function convergence lemma from `WeakConvergence.lean`.
-/
import Mathlib
import HDP.CharFunTaylor
import HDP.WeakConvergence

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal BigOperators Topology

namespace HDP


lemma charFun_const_mul_map {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Ω → ℝ) (c t : ℝ) (hS : AEMeasurable S μ) :
    charFun (μ.map (fun ω => c * S ω)) t = charFun (μ.map S) (c * t) := by
  change charFun (μ.map ((fun x : ℝ => c * x) ∘ S)) t = charFun (μ.map S) (c * t)
  rw [← AEMeasurable.map_map_of_aemeasurable (g := fun x : ℝ => c * x) (f := S)
    (by fun_prop : AEMeasurable (fun x : ℝ => c * x) (μ.map S)) hS]
  simpa using (charFun_map_mul (μ := μ.map S) c t)

lemma charFun_sum_fin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ} (Y : Fin N → Ω → ℝ) (hY : iIndepFun Y μ)
    (hYm : ∀ i, AEMeasurable (Y i) μ) (t : ℝ) :
    charFun (μ.map (fun ω => ∑ i : Fin N, Y i ω)) t =
      ∏ i : Fin N, charFun (μ.map (Y i)) t := by
  have h := congrFun (iIndepFun.charFun_map_sum_eq_prod (P := μ) (X := Y) hYm hY) t
  rw [show (∑ i : Fin N, Y i) = (fun ω => ∑ i : Fin N, Y i ω) from by ext ω; simp] at h
  simpa [Finset.prod_apply] using h

lemma clt_charFun_scalar_limit {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h2 : MemLp (fun x : ℝ => x) 2 ν) (hmean : ∫ x, x ∂ν = 0)
    (σ : ℝ) (hσ : 0 < σ) (hvar : ∫ x, x^2 ∂ν = σ^2) (t : ℝ) :
    Tendsto (fun N : ℕ => (N : ℂ) * (charFun ν (t / (σ * Real.sqrt (N : ℝ))) - 1))
      atTop (𝓝 (-(t : ℂ)^2 / 2)) := by
  by_cases ht : t = 0
  · subst t
    simp
  let s : ℕ → ℝ := fun N => t / (σ * Real.sqrt (N : ℝ))
  have hden : Tendsto (fun N : ℕ => σ * Real.sqrt (N : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hσ
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hsne : ∀ᶠ N : ℕ in atTop, s N ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hsqrt : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNpos
    have hdenpos : 0 < σ * Real.sqrt (N:ℝ) := mul_pos hσ hsqrt
    exact div_ne_zero ht (ne_of_gt hdenpos)
  have hsn : Tendsto s atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hs0, hsne⟩
  have hratio : Tendsto (fun y : ℝ => (charFun ν y - 1) / (y : ℂ)^2) (𝓝[≠] (0:ℝ))
      (𝓝 (-(σ^2 : ℂ) / 2)) := by
    have h := charFun_centered_taylor (ν := ν) h2 hmean
    rw [hvar] at h
    simpa [map_pow] using h
  have hcomp : Tendsto (fun N : ℕ => (charFun ν (s N) - 1) / (s N : ℂ)^2) atTop
      (𝓝 (-(σ^2 : ℂ) / 2)) := hratio.comp hsn
  have hNs : Tendsto (fun N : ℕ => ((N : ℝ) * (s N)^2 : ℂ)) atTop (𝓝 ((t^2 / σ^2 : ℝ) : ℂ)) := by
    have hreal : Tendsto (fun N : ℕ => (N : ℝ) * (s N)^2) atTop (𝓝 (t^2 / σ^2)) := by
      have heq : ∀ᶠ N : ℕ in atTop, (N : ℝ) * (s N)^2 = t^2 / σ^2 := by
        filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
        have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
        have hsqrt : (Real.sqrt (N:ℝ))^2 = (N:ℝ) := Real.sq_sqrt hNpos.le
        have hden : σ * Real.sqrt (N:ℝ) ≠ 0 := by
          exact mul_ne_zero hσ.ne' (ne_of_gt (Real.sqrt_pos.mpr hNpos))
        simp only [s]
        field_simp [hden, hσ.ne']
        rw [hsqrt]
      exact tendsto_const_nhds.congr' (heq.mono fun N h => h.symm)
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _ |>.comp hreal)
  have hprod := hNs.mul hcomp
  have hlimval : ((t^2 / σ^2 : ℝ) : ℂ) * (-(σ^2 : ℂ) / 2) = -(t : ℂ)^2 / 2 := by
    push_cast
    field_simp [hσ.ne']
  rw [hlimval] at hprod
  refine hprod.congr' ?_
  filter_upwards [hsne] with N hN
  have hNc : (N : ℂ) = ((N : ℝ) : ℂ) := by norm_num
  rw [hNc]
  field_simp [hN]
  ring



lemma charFun_normalized_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (N : ℕ) (t : ℝ) :
    charFun (μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N : ℝ)))) t =
      (charFun (μ.map (fun ω => X 0 ω - m)) (t / (σ * Real.sqrt (N : ℝ)))) ^ N := by
  let Y : Fin N → Ω → ℝ := fun i ω => X (i : ℕ) ω - m
  have hYmeas : ∀ i, AEMeasurable (Y i) μ := fun i => (hX (i:ℕ)).1.aemeasurable.sub_const m
  have hYind : iIndepFun Y μ := by
    have hpre : iIndepFun (fun i : Fin N => X (i:ℕ)) μ :=
      hindep.precomp (g := fun i : Fin N => (i:ℕ)) (fun _ _ h => Fin.ext h)
    exact hpre.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have hsum_meas : AEMeasurable (fun ω => ∑ i : Fin N, Y i ω) μ := by
    classical
    refine Finset.induction_on (Finset.univ : Finset (Fin N)) ?_ ?_
    · simpa using aemeasurable_const
    · intro a s ha ih
      simpa [Finset.sum_insert ha] using (hYmeas a).add ih
  have hscale := charFun_const_mul_map (μ := μ) (fun ω => ∑ i : Fin N, Y i ω)
    ((σ * Real.sqrt (N : ℝ))⁻¹) t hsum_meas
  rw [show (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N : ℝ))) =
      fun ω => (σ * Real.sqrt (N : ℝ))⁻¹ * (∑ i : Fin N, Y i ω) by
    ext ω; simp [Y, div_eq_mul_inv]; ring]
  rw [hscale]
  have hprod := charFun_sum_fin (Y := Y) hYind hYmeas ((σ * Real.sqrt (N : ℝ))⁻¹ * t)
  rw [hprod]
  have hconst : ∀ i : Fin N, charFun (μ.map (Y i)) ((σ * Real.sqrt (N : ℝ))⁻¹ * t) =
      charFun (μ.map (fun ω => X 0 ω - m)) ((σ * Real.sqrt (N : ℝ))⁻¹ * t) := by
    intro i
    have hmap : μ.map (Y i) = μ.map (fun ω => X 0 ω - m) := by
      have hcomp := (hident (i:ℕ)).comp (measurable_id.sub_const m)
      simpa [Y, Function.comp_def] using hcomp.map_eq
    rw [hmap]
  rw [Finset.prod_congr rfl (fun i _ => hconst i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  rw [show (σ * Real.sqrt (N : ℝ))⁻¹ * t = t / (σ * Real.sqrt (N : ℝ)) by ring]



lemma centered_law_properties {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = m)
    (hvar : ∀ i, variance (X i) μ = σ^2) :
    let ν : Measure ℝ := μ.map (fun ω => X 0 ω - m)
    MemLp (fun x : ℝ => x) 2 ν ∧ (∫ x, x ∂ν = 0) ∧ (∫ x, x^2 ∂ν = σ^2) := by
  dsimp only
  let Y : Ω → ℝ := fun ω => X 0 ω - m
  have hYmem : MemLp Y 2 μ := (hX 0).sub (memLp_const m)
  have hYint : Integrable Y μ := memLp_two_integrable hYmem
  have hYmeas : AEMeasurable Y μ := hYmem.aemeasurable
  have hYmean : ∫ ω, Y ω ∂μ = 0 := by
    rw [show Y = fun ω => X 0 ω - m from rfl, integral_sub (memLp_two_integrable (hX 0)) (integrable_const m)]
    simp [hmean 0]
  have hνmean : ∫ x, x ∂(μ.map Y) = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simpa [Y] using hYmean
  have hYvar : variance Y μ = σ^2 := by
    rw [show Y = fun ω => X 0 ω - m from rfl, variance_sub_const (hX 0).1 m, hvar 0]
  have hνvar : ∫ x, x^2 ∂(μ.map Y) = σ^2 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    calc
      ∫ x, Y x ^ 2 ∂μ = variance Y μ := by
        rw [variance_eq_integral hYmeas]
        simp [hYmean]
      _ = σ^2 := hYvar
  have hνmem : MemLp (fun x : ℝ => x) 2 (μ.map Y) := by
    rw [memLp_map_measure_iff (by fun_prop) hYmeas]
    simpa using hYmem
  exact ⟨hνmem, hνmean, hνvar⟩



theorem charFun_Z_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ^2)
    (t : ℝ) :
    Tendsto (fun N : ℕ =>
      charFun (μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)))) t)
      atTop (𝓝 (cexp (-(t:ℂ)^2 / 2))) := by
  let Y : Ω → ℝ := fun ω => X 0 ω - m
  let ν : Measure ℝ := μ.map Y
  haveI hνprob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (((hX 0).aemeasurable).sub_const m)
  have hYprops := centered_law_properties (μ := μ) X m σ hX hmean hvar
  have hνmem : MemLp (fun x : ℝ => x) 2 ν := hYprops.1
  have hνmean : ∫ x, x ∂ν = 0 := hYprops.2.1
  have hνvar : ∫ x, x^2 ∂ν = σ^2 := hYprops.2.2
  have hscalar := clt_charFun_scalar_limit (ν := ν) hνmem hνmean σ hσ hνvar t
  have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto
    (g := fun N : ℕ => charFun ν (t / (σ * Real.sqrt (N:ℝ))) - 1) hscalar
  refine hpow.congr' ?_
  filter_upwards with N
  have hchar := charFun_normalized_sum (μ := μ) X m σ hσ hX hindep hident N t
  change (1 + (charFun ν (t / (σ * Real.sqrt (N:ℝ))) - 1)) ^ N =
    charFun (μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)))) t
  rw [hchar]
  congr 1
  ring



lemma variance_Z {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hvar : ∀ i, variance (X i) μ = σ^2) {N : ℕ} (hN : 0 < N) :
    variance (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))) μ = 1 := by
  let Y : Fin N → Ω → ℝ := fun i ω => X (i:ℕ) ω - m
  have hYmem : ∀ i, MemLp (Y i) 2 μ := fun i => (hX (i:ℕ)).sub (memLp_const m)
  have hYind : iIndepFun Y μ := by
    have hpre : iIndepFun (fun i : Fin N => X (i:ℕ)) μ :=
      hindep.precomp (g := fun i : Fin N => (i:ℕ)) (fun _ _ h => Fin.ext h)
    exact hpre.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have hsumvar : variance (fun ω => ∑ i : Fin N, Y i ω) μ =
      ∑ i : Fin N, variance (Y i) μ := by
    have h := IndepFun.variance_sum (s := Finset.univ) (X := Y)
      (fun i _ => hYmem i) (fun i _ j _ hij => hYind.indepFun hij)
    rwa [show (∑ i : Fin N, Y i) = (fun ω => ∑ i : Fin N, Y i ω) from by ext ω; simp] at h
  have hYvar : ∀ i : Fin N, variance (Y i) μ = σ^2 := fun i => by
    rw [show Y i = fun ω => X (i:ℕ) ω - m from rfl, variance_sub_const (hX (i:ℕ)).1 m, hvar]
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hsqrt : (Real.sqrt (N:ℝ))^2 = (N:ℝ) := Real.sq_sqrt hNpos.le
  have hden : σ * Real.sqrt (N:ℝ) ≠ 0 :=
    mul_ne_zero hσ.ne' (ne_of_gt (Real.sqrt_pos.mpr hNpos))
  have hZeq : (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))) =
      fun ω => (σ * Real.sqrt (N:ℝ))⁻¹ * (∑ i : Fin N, Y i ω) := by
    ext ω; simp [Y, div_eq_mul_inv]; ring
  rw [hZeq, variance_const_mul, hsumvar]
  rw [Finset.sum_congr rfl (fun i _ => hYvar i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hden, hσ.ne', hNpos.ne']
  rw [hsqrt]



lemma mean_Z {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = m)
    (N : ℕ) :
    ∫ ω, (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)) ∂μ = 0 := by
  have hYint : ∀ i : Fin N, Integrable (fun ω => X (i:ℕ) ω - m) μ :=
    fun i => memLp_two_integrable ((hX (i:ℕ)).sub (memLp_const m))
  have hYmean : ∀ i : Fin N, ∫ ω, (X (i:ℕ) ω - m) ∂μ = 0 := by
    intro i
    rw [integral_sub (memLp_two_integrable (hX (i:ℕ))) (integrable_const m)]
    simp [hmean]
  have hsum : ∫ ω, (∑ i : Fin N, (X i ω - m)) ∂μ = 0 := by
    rw [integral_finset_sum _ (fun i _ => hYint i)]
    simp [hYmean]
  rw [show (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))) =
      fun ω => (σ * Real.sqrt (N:ℝ))⁻¹ * (∑ i : Fin N, (X i ω - m)) by
    ext ω; rw [div_eq_mul_inv]; ring]
  rw [integral_const_mul, hsum]
  simp

lemma memLp_Z {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (N : ℕ) :
    MemLp (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))) 2 μ := by
  have hsum : MemLp (fun ω => ∑ i : Fin N, (X i ω - m)) 2 μ :=
    memLp_finset_sum (s := Finset.univ) (fun i _ => (hX (i:ℕ)).sub (memLp_const m))
  have := hsum.const_mul ((σ * Real.sqrt (N:ℝ))⁻¹)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this



lemma measure_norm_gt_Z_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ^2)
    {r : ℝ} (hr : 0 < r) (N : ℕ) :
    (μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)))) {x | r < ‖x‖} ≤
      ENNReal.ofReal (1 / r^2) := by
  let Z : Ω → ℝ := fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))
  by_cases hN : N = 0
  · subst N
    have hZ0 : Z = fun _ => 0 := by
      funext ω
      simp [Z]
    change (μ.map Z) {x | r < ‖x‖} ≤ ENNReal.ofReal (1 / r^2)
    rw [hZ0, Measure.map_const]
    simp only [Measure.smul_apply, measure_univ, one_smul]
    rw [Measure.dirac_apply]
    rw [Set.indicator_of_notMem]
    · exact zero_le _
    · simp only [Set.mem_setOf_eq, norm_zero]
      linarith
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hZmem : MemLp Z 2 μ := memLp_Z X m σ hX N
    have hZmean : ∫ ω, Z ω ∂μ = 0 := mean_Z X m σ hσ hX hmean N
    have hZmeas : AEMeasurable Z μ := hZmem.aemeasurable
    rw [show (μ.map Z) {x : ℝ | r < ‖x‖} = μ {ω | r < ‖Z ω‖} by
      rw [Measure.map_apply_of_aemeasurable hZmeas]
      · rfl
      · exact measurableSet_lt measurable_const measurable_norm]
    have hsub : {ω | r < ‖Z ω‖} ⊆ {ω | r ≤ |Z ω - μ[Z]|} := by
      intro ω h
      have h' : r < |Z ω| := by simpa [Real.norm_eq_abs] using h
      rw [hZmean]
      simpa using h'.le
    calc
      μ {ω | r < ‖Z ω‖} ≤ μ {ω | r ≤ |Z ω - μ[Z]|} := measure_mono hsub
      _ ≤ ENNReal.ofReal (variance Z μ / r^2) := meas_ge_le_variance_div_sq hZmem hr
      _ = ENNReal.ofReal (1 / r^2) := by
        rw [variance_Z X m σ hσ hX hindep hvar hNpos]



theorem tight_Z {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ^2) :
    IsTightMeasureSet (Set.range fun N =>
      μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)))) := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  simp only [iSup_range]
  have hreal : Tendsto (fun r : ℝ => (1 / r^2 : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r⁻¹ * r⁻¹) atTop (𝓝 (0 * 0)) :=
      tendsto_inv_atTop_zero.mul tendsto_inv_atTop_zero
    rw [show (0 * 0 : ℝ) = 0 by norm_num] at h
    simpa [div_eq_mul_inv, pow_two] using h
  have hENN : Tendsto (fun r : ℝ => ENNReal.ofReal (1 / r^2)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hreal
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hENN ?_ ?_
  · filter_upwards with r
    exact zero_le _
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact ciSup_le fun N => measure_norm_gt_Z_le X m σ hσ hX hindep hmean hvar hr N



theorem central_limit_theorem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ^2) :
    let Z : ℕ → Ω → ℝ := fun N ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))
    let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
      ⟨μ.map (Z N), Measure.isProbabilityMeasure_map (memLp_Z X m σ hX N).aemeasurable⟩
    let gauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
    Tendsto νs atTop (𝓝 gauss) := by
  dsimp only
  let Z : ℕ → Ω → ℝ := fun N ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))
  let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨μ.map (Z N), Measure.isProbabilityMeasure_map (memLp_Z X m σ hX N).aemeasurable⟩
  let gauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  change Tendsto νs atTop (𝓝 gauss)
  have htight : IsTightMeasureSet {((νs N : ProbabilityMeasure ℝ) : Measure ℝ) | N} := by
    simpa [νs, Z] using tight_Z X m σ hσ hX hindep hmean hvar
  have hchar : ∀ t : ℝ, Tendsto (fun N => charFun (νs N : Measure ℝ) t) atTop
      (𝓝 (charFun (gauss : Measure ℝ) t)) := by
    intro t
    have h := charFun_Z_tendsto X m σ hσ hX hindep hident hmean hvar t
    have hgauss : charFun (gaussianReal 0 1 : Measure ℝ) t = cexp (-(t : ℂ)^2 / 2) := by
      have h0 := charFun_gaussianReal (μ := 0) (v := 1) t
      simpa [neg_div] using h0
    change Tendsto (fun N => charFun (νs N : Measure ℝ) t) atTop
      (𝓝 (charFun (gaussianReal 0 1 : Measure ℝ) t))
    rw [hgauss]
    simpa [νs, Z] using h
  exact tendsto_probabilityMeasure_of_charFun νs gauss htight hchar



theorem central_limit_cdf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ^2)
    (t : ℝ) :
    Tendsto (fun N : ℕ =>
      (μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)))).real (Set.Iic t))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic t))) := by
  let Z : ℕ → Ω → ℝ := fun N ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))
  let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨μ.map (Z N), Measure.isProbabilityMeasure_map (memLp_Z X m σ hX N).aemeasurable⟩
  let gauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hlim := central_limit_theorem X m σ hσ hX hindep hident hmean hvar
  dsimp only at hlim
  have hsing : (gaussianReal 0 1 : Measure ℝ) {t} = 0 := by
    rw [gaussianReal_apply 0 (by norm_num) {t}]
    simp
  have hfront : (gaussianReal 0 1 : Measure ℝ) (frontier (Set.Iic t)) = 0 := by
    apply measure_mono_null _ hsing
    intro x hx
    simpa [frontier_Iic] using hx
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := νs) (μ := gauss) hlim (E := Set.Iic t) (by simpa [gauss] using hfront)
  have hfinite : (gauss : Measure ℝ) (Set.Iic t) ≠ ∞ := measure_ne_top _ _
  have htoReal := ENNReal.tendsto_toReal hfinite |>.comp hmeasure
  simpa [νs, gauss, Z, Measure.real] using htoReal


theorem central_limit_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (m σ : ℝ) (hσ : 0 < σ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = m) (hvar : ∀ i, variance (X i) μ = σ^2)
    (t : ℝ) :
    Tendsto (fun N : ℕ =>
      (μ.map (fun ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ)))).real (Set.Ici t))
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Ici t))) := by
  let Z : ℕ → Ω → ℝ := fun N ω => (∑ i : Fin N, (X i ω - m)) / (σ * Real.sqrt (N:ℝ))
  let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨μ.map (Z N), Measure.isProbabilityMeasure_map (memLp_Z X m σ hX N).aemeasurable⟩
  let gauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hlim := central_limit_theorem X m σ hσ hX hindep hident hmean hvar
  dsimp only at hlim
  have hsing : (gaussianReal 0 1 : Measure ℝ) {t} = 0 := by
    rw [gaussianReal_apply 0 (by norm_num) {t}]
    simp
  have hfront : (gaussianReal 0 1 : Measure ℝ) (frontier (Set.Ici t)) = 0 := by
    apply measure_mono_null _ hsing
    intro x hx
    simpa [frontier_Ici] using hx
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := νs) (μ := gauss) hlim (E := Set.Ici t) (by simpa [gauss] using hfront)
  have hfinite : (gauss : Measure ℝ) (Set.Ici t) ≠ ∞ := measure_ne_top _ _
  have htoReal := ENNReal.tendsto_toReal hfinite |>.comp hmeasure
  simpa [νs, gauss, Z, Measure.real] using htoReal

end HDP
