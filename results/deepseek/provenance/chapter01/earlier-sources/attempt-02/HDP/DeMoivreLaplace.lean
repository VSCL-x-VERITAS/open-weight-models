/-
The de Moivre--Laplace theorem, as the Bernoulli special case of the CLT.
-/
import Mathlib
import HDP.CLT

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal BigOperators Topology

namespace HDP

lemma bernoulli_id_memLp (p : ℝ≥0) (hp : p ≤ 1) :
    MemLp (fun x : ℝ => x) 2 (bernoulliMeasure p) := by
  haveI : IsProbabilityMeasure (bernoulliMeasure p) := bernoulliMeasure_isProbability p hp
  refine MemLp.of_bound (by fun_prop) 1 ?_
  have hnull : bernoulliMeasure p {x : ℝ | ¬ (x = 0 ∨ x = 1)} = 0 := by
    simp [bernoulliMeasure]
  have hae : ∀ᵐ x ∂bernoulliMeasure p, x = 0 ∨ x = 1 := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hae] with x hx
  rcases hx with rfl | rfl <;> norm_num

theorem de_moivre_laplace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (p : ℝ≥0) (hp0 : 0 < p) (hp1 : p < 1)
    (hXmeas : ∀ i, AEMeasurable (X i) μ) (hindep : iIndepFun X μ)
    (hXlaw : ∀ i, μ.map (X i) = bernoulliMeasure p) :
    let σ : ℝ := Real.sqrt ((p : ℝ) * (1 - (p : ℝ)))
    let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
      ⟨μ.map (fun ω => (∑ i : Fin N, (X i ω - (p:ℝ))) / (σ * Real.sqrt (N:ℝ))),
        Measure.isProbabilityMeasure_map (memLp_Z X (p:ℝ) σ (fun i => by
          have hid := bernoulli_id_memLp p hp1.le
          have hmap : MemLp (fun x : ℝ => x) 2 (μ.map (X i)) := by rw [hXlaw i]; exact hid
          have := (memLp_map_measure_iff (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x) (μ.map (X i))) (hXmeas i)).mp hmap
          simpa using this) N).aemeasurable⟩
    let gauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
    Tendsto νs atTop (𝓝 gauss) := by
  dsimp only
  let σ : ℝ := Real.sqrt ((p : ℝ) * (1 - (p : ℝ)))
  let νs : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨μ.map (fun ω => (∑ i : Fin N, (X i ω - (p:ℝ))) / (σ * Real.sqrt (N:ℝ))),
      Measure.isProbabilityMeasure_map (memLp_Z X (p:ℝ) σ (fun i => by
        have hid := bernoulli_id_memLp p hp1.le
        have hmap : MemLp (fun x : ℝ => x) 2 (μ.map (X i)) := by rw [hXlaw i]; exact hid
        have := (memLp_map_measure_iff (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x) (μ.map (X i))) (hXmeas i)).mp hmap
        simpa using this) N).aemeasurable⟩
  let gauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  change Tendsto νs atTop (𝓝 gauss)
  have hp : p ≤ 1 := hp1.le
  have hσ : 0 < σ := by
    rw [show σ = Real.sqrt ((p:ℝ) * (1-(p:ℝ))) from rfl]
    apply Real.sqrt_pos.mpr
    have hp0' : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp0
    have hp1' : (p:ℝ) < 1 := by exact_mod_cast hp1
    nlinarith
  have hid := bernoulli_id_memLp p hp
  have hXmem : ∀ i, MemLp (X i) 2 μ := by
    intro i
    have hmap : MemLp (fun x : ℝ => x) 2 (μ.map (X i)) := by rw [hXlaw i]; exact hid
    have := (memLp_map_measure_iff (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x) (μ.map (X i))) (hXmeas i)).mp hmap
    simpa using this
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := by
    intro i
    exact ⟨hXmeas i, hXmeas 0, by rw [hXlaw i, hXlaw 0]⟩
  have hmean : ∀ i, ∫ ω, X i ω ∂μ = (p:ℝ) := by
    intro i
    rw [← integral_map (hXmeas i) (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x) (μ.map (X i))), hXlaw i]
    simpa using bernoulli_mean p hp
  have hvar : ∀ i, variance (X i) μ = (p:ℝ) * (1 - (p:ℝ)) := by
    intro i
    have h1 : variance (fun x : ℝ => x) (μ.map (X i)) = variance (X i) μ := by
      simpa using (variance_map (by fun_prop : AEMeasurable (fun x:ℝ=>x) (μ.map (X i))) (hXmeas i))
    rw [← h1, hXlaw i, bernoulli_variance p hp]
  have hvarσ : ∀ i, variance (X i) μ = σ^2 := by
    intro i
    rw [hvar i]
    rw [show σ^2 = (p:ℝ) * (1-(p:ℝ)) by
      rw [show σ = Real.sqrt ((p:ℝ) * (1-(p:ℝ))) from rfl, Real.sq_sqrt]
      exact mul_nonneg (by exact_mod_cast hp0.le) (by
        have : (p:ℝ) < 1 := by exact_mod_cast hp1
        linarith)]
  have hmain := central_limit_theorem X (p:ℝ) σ hσ hXmem hindep hident hmean hvarσ
  exact hmain

end HDP