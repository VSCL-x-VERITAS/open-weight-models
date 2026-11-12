/-
Weak convergence of probability measures on `ℝ` from pointwise convergence of
characteristic functions, using Prokhorov compactness and uniqueness of the
characteristic function.  This is the part of a Lévy continuity theorem needed
for the CLT and Poisson limit.
-/
import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HDP

lemma charFun_tendsto_of_tendsto {νs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : Tendsto νs atTop (𝓝 ν)) (t : ℝ) :
    Tendsto (fun n => charFun (νs n : Measure ℝ) t) atTop (𝓝 (charFun (ν : Measure ℝ) t)) := by
  have hbc := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h
    (BoundedContinuousFunction.innerProbChar t)
  simpa only [charFun_eq_integral_innerProbChar] using hbc

theorem tendsto_probabilityMeasure_of_charFun
    (νs : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (htight : IsTightMeasureSet {((νs n : ProbabilityMeasure ℝ) : Measure ℝ) | n})
    (hchar : ∀ t, Tendsto (fun n => charFun (νs n : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t))) :
    Tendsto νs atTop (𝓝 ν) := by
  by_contra h
  rw [tendsto_nhds] at h
  push_neg at h
  obtain ⟨U, hUopen, hμU, hfreq⟩ := h
  let S : Set (ProbabilityMeasure ℝ) := closure (Set.range νs)
  have hS : IsCompact S := isCompact_closure_of_isTightMeasureSet (by simpa [S] using htight)
  have hclosed : IsClosed Uᶜ := hUopen.isClosed_compl
  have hcomp : IsCompact (S ∩ Uᶜ) := hS.inter_right hclosed
  have hfreq_not : ∃ᶠ n in atTop, νs n ∉ U := by
    change ¬ ∀ᶠ n in atTop, ¬ (νs n ∉ U)
    simpa using hfreq
  have hfreq' : ∃ᶠ n in atTop, νs n ∈ S ∩ Uᶜ := by
    exact hfreq_not.mono fun n hn => ⟨subset_closure (Set.mem_range_self n), hn⟩
  obtain ⟨a, ha, φ, hφ, htend⟩ := hcomp.tendsto_subseq' hfreq'
  have hchar_a : ∀ t, Tendsto (fun k => charFun (νs (φ k) : Measure ℝ) t) atTop
      (𝓝 (charFun (a : Measure ℝ) t)) := fun t =>
    charFun_tendsto_of_tendsto (νs := fun k => νs (φ k)) (ν := a) htend t
  have hchar_ν : ∀ t, Tendsto (fun k => charFun (νs (φ k) : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t)) := fun t =>
    (hchar t).comp hφ.tendsto_atTop
  have heq : a = ν := by
    haveI : IsFiniteMeasure (a : Measure ℝ) := ⟨by
      rw [IsProbabilityMeasure.measure_univ (μ := (a : Measure ℝ))]
      exact ENNReal.one_lt_top⟩
    haveI : IsFiniteMeasure (ν : Measure ℝ) := ⟨by
      rw [IsProbabilityMeasure.measure_univ (μ := (ν : Measure ℝ))]
      exact ENNReal.one_lt_top⟩
    apply Subtype.ext
    have hchar_eq : charFun (a : Measure ℝ) = charFun (ν : Measure ℝ) := by
      funext t
      exact tendsto_nhds_unique (hchar_a t) (hchar_ν t)
    exact Measure.ext_of_charFun (μ := (a : Measure ℝ)) (ν := (ν : Measure ℝ)) hchar_eq
  exact ha.2 (by simpa [heq] using hμU)

end HDP
