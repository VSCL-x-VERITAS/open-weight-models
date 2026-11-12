/-
Theorem 1.3.4: the Poisson limit theorem for triangular arrays of independent
Bernoulli variables.
-/
import Mathlib
import HDP.DeMoivreLaplace
import HDP.PoissonProduct
import HDP.WeakConvergence

open Finset Filter Topology Complex MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators Complex

namespace HDP

lemma charFun_sum_bernoulli_row {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (p : ℕ → ℕ → ℝ≥0)
    (hXmeas : ∀ N i, AEMeasurable (X N i) μ)
    (hXlaw : ∀ N i, μ.map (X N i) = bernoulliMeasure (p N i))
    (hp : ∀ N i, p N i ≤ 1)
    (hrow : ∀ N, iIndepFun (fun i : Fin N => X N i) μ) (N : ℕ) (t : ℝ) :
    charFun (μ.map (fun ω => ∑ i : Fin N, X N i ω)) t =
      ∏ i : Fin N, ((1 - (p N i : ℂ)) + (p N i : ℂ) * cexp ((t:ℂ) * Complex.I)) := by
  rw [charFun_sum_fin (Y := fun i : Fin N => X N i) (hrow N) (fun i => hXmeas N i) t]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hXlaw N i, charFun_bernoulli (p N i) (hp N i) t]

lemma ae_nonneg_of_map_bernoulli {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {p : ℝ≥0} (hX : AEMeasurable X μ)
    (h : μ.map X = bernoulliMeasure p) : 0 ≤ᵐ[μ] X := by
  change ∀ᵐ ω ∂μ, 0 ≤ X ω
  rw [ae_iff]
  have hset : μ {ω | ¬ 0 ≤ X ω} = (μ.map X) (Set.Iio 0) := by
    rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iio]
    congr 1
    ext ω
    simp [Set.Iio]
  rw [hset, h]
  simp [bernoulliMeasure]

lemma memLp_of_map_bernoulli {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {p : ℝ≥0} (hX : AEMeasurable X μ)
    (h : μ.map X = bernoulliMeasure p) (hp : p ≤ 1) : MemLp X 2 μ := by
  have hid := bernoulli_id_memLp p hp
  have hmap : MemLp (fun x : ℝ => x) 2 (μ.map X) := by rw [h]; exact hid
  have := (memLp_map_measure_iff (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x) (μ.map X)) hX).mp hmap
  simpa using this

lemma integral_of_map_bernoulli {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℝ≥0} (hX : AEMeasurable X μ)
    (h : μ.map X = bernoulliMeasure p) (hp : p ≤ 1) : ∫ ω, X ω ∂μ = (p:ℝ) := by
  rw [← integral_map hX (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x) (μ.map X)), h]
  simpa using bernoulli_mean p hp

lemma ae_nonneg_sum_row {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (p : ℕ → ℕ → ℝ≥0)
    (hXmeas : ∀ N i, AEMeasurable (X N i) μ)
    (hXlaw : ∀ N i, μ.map (X N i) = bernoulliMeasure (p N i)) (N : ℕ) :
    0 ≤ᵐ[μ] (fun ω => ∑ i : Fin N, X N i ω) := by
  have hx : ∀ i : Fin N, 0 ≤ᵐ[μ] X N i := fun i =>
    ae_nonneg_of_map_bernoulli (hXmeas N i) (hXlaw N i)
  filter_upwards [ae_all_iff.2 hx] with ω hω
  exact Finset.sum_nonneg fun i hi => hω i

lemma integral_sum_row {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (p : ℕ → ℕ → ℝ≥0)
    (hXmeas : ∀ N i, AEMeasurable (X N i) μ)
    (hXlaw : ∀ N i, μ.map (X N i) = bernoulliMeasure (p N i))
    (hp : ∀ N i, p N i ≤ 1) (N : ℕ) :
    ∫ ω, (∑ i : Fin N, X N i ω) ∂μ = ∑ i : Fin N, (p N i : ℝ) := by
  change ∫ ω, (∑ i ∈ (Finset.univ : Finset (Fin N)), X N i ω) ∂μ =
    ∑ i ∈ (Finset.univ : Finset (Fin N)), (p N i : ℝ)
  have h := integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (Fin N)))
    (f := fun i ω => X N i ω)
    (fun i hi => memLp_two_integrable (memLp_of_map_bernoulli (hXmeas N i) (hXlaw N i) (hp N i)))
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_of_map_bernoulli (hXmeas N i) (hXlaw N i) (hp N i)

lemma integrable_sum_row {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (p : ℕ → ℕ → ℝ≥0)
    (hXmeas : ∀ N i, AEMeasurable (X N i) μ)
    (hXlaw : ∀ N i, μ.map (X N i) = bernoulliMeasure (p N i))
    (hp : ∀ N i, p N i ≤ 1) (N : ℕ) :
    Integrable (fun ω => ∑ i : Fin N, X N i ω) μ := by
  have hmem : MemLp (fun ω => ∑ i : Fin N, X N i ω) 2 μ := by
    classical
    exact memLp_finset_sum (s := (Finset.univ : Finset (Fin N)))
      (fun i _ => memLp_of_map_bernoulli (hXmeas N i) (hXlaw N i) (hp N i))
  exact memLp_two_integrable hmem

lemma exists_sum_bound (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) atTop (𝓝 (lam:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∑ i ∈ Finset.range N, (p N i : ℝ) ≤ C := by
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (hsum.eventually (Iio_mem_nhds (lt_add_one (lam:ℝ))))
  let S0 : ℝ := ∑ M ∈ Finset.range N0, ∑ i ∈ Finset.range M, (p M i : ℝ)
  let C : ℝ := ((lam:ℝ) + 1) + S0
  refine ⟨C, ?_, ?_⟩
  · have hS0 : 0 ≤ S0 := Finset.sum_nonneg fun M hM => Finset.sum_nonneg fun i hi => (p M i).coe_nonneg
    have hlam : 0 ≤ (lam:ℝ) := lam.coe_nonneg
    dsimp [C]; linarith
  · intro N
    by_cases hN : N < N0
    · have hmem : N ∈ Finset.range N0 := Finset.mem_range.mpr hN
      have hsingle : ∑ i ∈ Finset.range N, (p N i : ℝ) ≤ S0 := by
        apply Finset.single_le_sum (f := fun M => ∑ i ∈ Finset.range M, (p M i : ℝ))
        · intro M hM
          exact Finset.sum_nonneg fun i hi => (p M i).coe_nonneg
        · exact hmem
      dsimp [C]
      linarith [show 0 ≤ (lam:ℝ) + 1 by positivity]
    · have hN0le : N0 ≤ N := le_of_not_gt hN
      have hlt := hN0 N hN0le
      dsimp [C]
      have hS0 : 0 ≤ S0 := Finset.sum_nonneg fun M hM => Finset.sum_nonneg fun i hi => (p M i).coe_nonneg
      linarith


theorem tight_poisson_sums {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0)
    (hXmeas : ∀ N i, AEMeasurable (X N i) μ)
    (hXlaw : ∀ N i, μ.map (X N i) = bernoulliMeasure (p N i))
    (hp : ∀ N i, p N i ≤ 1)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) atTop (𝓝 (lam:ℝ))) :
    IsTightMeasureSet (Set.range fun N => μ.map (fun ω => ∑ i : Fin N, X N i ω)) := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  simp only [iSup_range]
  obtain ⟨C, hC0, hC⟩ := exists_sum_bound p lam hsum
  have hreal : Tendsto (fun r : ℝ => C / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hENN : Tendsto (fun r : ℝ => ENNReal.ofReal (C / r)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hreal
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hENN ?_ ?_
  · filter_upwards with r; exact zero_le _
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    apply ciSup_le
    intro N
    let S : Ω → ℝ := fun ω => ∑ i : Fin N, X N i ω
    have hSmeas : AEMeasurable S μ := by
      have : AEMeasurable (fun ω => ∑ i : Fin N, X N i ω) μ := by
        classical
        refine Finset.induction_on (Finset.univ : Finset (Fin N)) ?_ ?_
        · simpa using aemeasurable_const
        · intro a s ha ih
          simpa [Finset.sum_insert ha] using (hXmeas N a).add ih
      exact this
    have hSint : Integrable S μ := integrable_sum_row X p hXmeas hXlaw hp N
    have hSnonneg : 0 ≤ᵐ[μ] S := ae_nonneg_sum_row X p hXmeas hXlaw N
    have hmap : (μ.map S) {x : ℝ | r < ‖x‖} = μ {ω | r < |S ω|} := by
      rw [Measure.map_apply_of_aemeasurable hSmeas (measurableSet_lt measurable_const measurable_norm)]
      rfl
    have hsub : {ω | r < |S ω|} ≤ᵐ[μ] {ω | r ≤ S ω} := by
      filter_upwards [hSnonneg] with ω hω h
      change r < |S ω| at h
      have habs : |S ω| = S ω := abs_of_nonneg hω
      rw [habs] at h
      exact h.le
    have hmark := markov (μ := μ) hSnonneg hSint hr
    rw [hmap]
    calc
      μ {ω | r < |S ω|} ≤ μ {ω | r ≤ S ω} := measure_mono_ae hsub
      _ = ENNReal.ofReal (μ.real {ω | r ≤ S ω}) := by
        rw [MeasureTheory.ofReal_measureReal]
      _ ≤ ENNReal.ofReal ((∫ ω, S ω ∂μ) / r) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [S] using hmark
      _ = ENNReal.ofReal (((∑ i : Fin N, (p N i : ℝ))) / r) := by
        rw [integral_sum_row X p hXmeas hXlaw hp N]
      _ ≤ ENNReal.ofReal (C / r) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ hr.le
        calc
          ∑ i : Fin N, (p N i : ℝ) = ∑ i ∈ Finset.range N, (p N i : ℝ) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mem_range.mp hi]
          _ ≤ C := hC N

lemma aemeasurable_sum_row {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → ℕ → Ω → ℝ) (hXmeas : ∀ N i, AEMeasurable (X N i) μ) (N : ℕ) :
    AEMeasurable (fun ω => ∑ i : Fin N, X N i ω) μ := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin N)) ?_ ?_
  · simpa using aemeasurable_const
  · intro a s ha ih
    simpa [Finset.sum_insert ha] using (hXmeas N a).add ih

theorem poisson_limit_theorem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (p : ℕ → ℕ → ℝ≥0) (lam : ℝ≥0)
    (hXmeas : ∀ N i, AEMeasurable (X N i) μ)
    (hXlaw : ∀ N i, μ.map (X N i) = bernoulliMeasure (p N i))
    (hrow : ∀ N, iIndepFun (fun i : Fin N => X N i) μ)
    (hp : ∀ N i, p N i ≤ 1)
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i < N, (p N i : ℝ) < ε)
    (hsum : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (p N i : ℝ)) atTop (𝓝 (lam:ℝ))) :
    let S : ℕ → Ω → ℝ := fun N ω => ∑ i : Fin N, X N i ω
    let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
      ⟨μ.map (S N), Measure.isProbabilityMeasure_map (aemeasurable_sum_row X hXmeas N)⟩
    let target : ProbabilityMeasure ℝ := ⟨poissonReal lam, inferInstance⟩
    Tendsto νs atTop (𝓝 target) := by
  dsimp only
  let S : ℕ → Ω → ℝ := fun N ω => ∑ i : Fin N, X N i ω
  let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨μ.map (S N), Measure.isProbabilityMeasure_map (aemeasurable_sum_row X hXmeas N)⟩
  let target : ProbabilityMeasure ℝ := ⟨poissonReal lam, inferInstance⟩
  change Tendsto νs atTop (𝓝 target)
  have htight : IsTightMeasureSet {((νs N : ProbabilityMeasure ℝ) : Measure ℝ) | N} := by
    simpa [νs, S] using tight_poisson_sums X p lam hXmeas hXlaw hp hsum
  have hchar : ∀ t : ℝ, Tendsto (fun N => charFun (νs N : Measure ℝ) t) atTop
      (𝓝 (charFun (target : Measure ℝ) t)) := by
    intro t
    let z : ℂ := cexp ((t:ℂ) * Complex.I)
    have hprod := poisson_product_tendsto p lam t hp hmax hsum
    have hconv : Tendsto (fun N : ℕ => charFun (μ.map (S N)) t) atTop
        (𝓝 (cexp ((lam:ℂ) * (z - 1)))) := by
      refine hprod.congr' ?_
      filter_upwards with N
      rw [show charFun (μ.map (S N)) t =
          ∏ i : Fin N, ((1 - (p N i : ℂ)) + (p N i : ℂ) * cexp ((t:ℂ) * Complex.I)) from
        charFun_sum_bernoulli_row X p hXmeas hXlaw hp hrow N t]
      rw [Finset.prod_fin_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    have htarget : charFun (poissonReal lam : Measure ℝ) t = cexp ((lam:ℂ) * (z - 1)) := by
      simpa [z, mul_comm, mul_left_comm, mul_assoc] using charFun_poissonReal lam t
    change Tendsto (fun N => charFun (νs N : Measure ℝ) t) atTop
      (𝓝 (charFun (poissonReal lam : Measure ℝ) t))
    rw [htarget]
    simpa [νs, S, z] using hconv
  exact tendsto_probabilityMeasure_of_charFun νs target htight hchar

end HDP
