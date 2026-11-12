/-
Section 1.3: variance of sums of independent variables, the strong law of large
numbers, Exercise 1.3.3, and the distributions used in the limit theorems.
-/
import Mathlib
import HDP.Basic
import HDP.Inequalities
import HDP.Tails

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal NNReal ProbabilityTheory BigOperators Function Topology

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The variance of a finite sum of pairwise independent random variables is the
sum of the variances. -/
theorem variance_sum_indep [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Set.Pairwise Set.univ fun i j => X i ⟂ᵢ[μ] X j) :
    variance (∑ i, X i) μ = ∑ i, variance (X i) μ := by
  simpa using IndepFun.variance_sum (s := Finset.univ)
    (fun i _ => hX i) (fun i _ j _ hij => hindep (Set.mem_univ i) (Set.mem_univ j) hij)

/-- Formula (1.5): for i.i.d. variables with variance `σ^2`, the sample mean has
variance `σ^2 / N`. -/
theorem variance_sampleMean [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {N : ℕ} (hN : 0 < N) :
    variance (sampleMean X N) μ = variance (X 0) μ / N := by
  have hsum : variance (fun ω => ∑ i ∈ Finset.range N, X i ω) μ =
      ∑ i ∈ Finset.range N, variance (X i) μ := by
    have h := IndepFun.variance_sum (s := Finset.range N)
      (fun i _ => hX i) (fun i _ j _ hij => hindep hij)
    rw [show (∑ i ∈ Finset.range N, X i) =
        (fun ω => ∑ i ∈ Finset.range N, X i ω) from by ext ω; simp] at h
    exact h
  have hconst : ∀ i ∈ Finset.range N, variance (X i) μ = variance (X 0) μ :=
    fun i _ => (hident i).variance_eq
  have hsam : sampleMean X N =
      fun ω => (N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, X i ω) := by
    ext ω
    simp [sampleMean, div_eq_inv_mul]
  rw [hsam, variance_const_mul, hsum, Finset.sum_congr rfl hconst]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNne]

/-- Theorem 1.3.1 (strong law of large numbers), using Mathlib's Etemadi proof. -/
theorem strong_law [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => sampleMean X N ω) atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  simpa [sampleMean] using strong_law_ae_real X hint hindep hident

/-- Expectation of the sample mean for identically distributed integrable variables. -/
theorem integral_sampleMean [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hint : ∀ i, Integrable (X i) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {N : ℕ} (hN : 0 < N) :
    ∫ ω, sampleMean X N ω ∂μ = ∫ ω, X 0 ω ∂μ := by
  have hsam : sampleMean X N =
      fun ω => (N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, X i ω) := by
    ext ω
    simp [sampleMean, div_eq_inv_mul]
  rw [hsam, integral_const_mul, integral_finset_sum]
  · have hsum : ∑ i ∈ Finset.range N, ∫ ω, X i ω ∂μ =
        (N : ℝ) * ∫ ω, X 0 ω ∂μ := by
      rw [Finset.sum_congr rfl (fun i _ => (hident i).integral_eq),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hNne]
  · intro i _
    exact hint i

/-- The Bernoulli distribution `Ber(p)` on `{0, 1}`, as a measure on `ℝ`. -/
noncomputable def bernoulliMeasure (p : ℝ≥0) : Measure ℝ :=
  (p : ℝ≥0∞) • Measure.dirac (1 : ℝ) + ((1 - p : ℝ≥0) : ℝ≥0∞) • Measure.dirac (0 : ℝ)

instance bernoulliMeasure_isProbability (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p) := by
  constructor
  simp only [bernoulliMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_univ, Pi.one_apply, smul_eq_mul, mul_one, MeasurableSet.univ]
  simp only [Set.indicator_of_mem, Set.mem_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add]
  congr 1
  exact add_tsub_cancel_of_le hp

/-- Mean of a Bernoulli variable: `E X = p`. -/
theorem bernoulli_mean (p : ℝ≥0) (hp : p ≤ 1) :
    ∫ x, x ∂bernoulliMeasure p = p := by
  rw [bernoulliMeasure, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp
  · exact (integrable_dirac (a := 1) (f := fun x : ℝ => x) (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (a := 0) (f := fun x : ℝ => x) (by simp)).smul_measure (by simp)

/-- Variance of a Bernoulli variable: `Var X = p (1 - p)`. -/
theorem bernoulli_variance (p : ℝ≥0) (hp : p ≤ 1) :
    variance (fun x : ℝ => x) (bernoulliMeasure p) = p * (1 - p) := by
  rw [variance_eq_integral (by fun_prop), bernoulli_mean p hp, bernoulliMeasure,
    integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp only [ENNReal.coe_toReal, smul_eq_mul]
    rw [NNReal.coe_sub hp]
    norm_num
    ring
  · exact (integrable_dirac (a := 1) (f := fun x : ℝ => (x - p) ^ 2)
      (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (a := 0) (f := fun x : ℝ => (x - p) ^ 2)
      (by simp)).smul_measure (by simp)

/-- The binomial distribution `Binom(N, p)` on `{0, ..., N}`, using Mathlib's
binomial PMF. -/
noncomputable def binomialMeasure (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Fin (N + 1)) :=
  (PMF.binomial p hp N).toMeasure

instance binomialMeasure_isProbability (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (binomialMeasure N p hp) := by
  unfold binomialMeasure
  infer_instance

/-- The Poisson distribution `Pois(λ)` (Mathlib's `poissonMeasure`). -/
noncomputable def poissonDist (r : ℝ≥0) : Measure ℕ := poissonMeasure r

/-- Formula (1.8): the Poisson mass function. -/
theorem poissonDist_apply (r : ℝ≥0) (k : ℕ) :
    poissonDist r {k} = ENNReal.ofReal (poissonPMFReal r k) := by
  rw [poissonDist, poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]
  simp [poissonPMF]
  rfl

theorem poissonPMFReal_eq (r : ℝ≥0) (k : ℕ) :
    poissonPMFReal r k = Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ) := by
  simp [poissonPMFReal]

/-- The standard normal density (1.6). -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = 1 / Real.sqrt (2 * Real.pi) * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal, one_div]

end HDP

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A function in `L^2` is integrable on a probability space. -/
lemma memLp_two_integrable [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact ⟨hf.1, lt_of_le_of_lt
    (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num) hf.1) hf.2⟩

/-- The empirical average as a scalar multiple of the partial sum. -/
lemma sampleMean_eq (X : ℕ → Ω → ℝ) (N : ℕ) :
    sampleMean X N = fun ω => (N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, X i ω) := by
  ext ω
  simp [sampleMean, div_eq_inv_mul]

/-- Exercise 1.3.3: the mean absolute deviation of the sample mean from the mean is
`O(1/√N)` for i.i.d. variables with finite variance. -/
theorem sampleMean_deviation_isBigO [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    (fun N : ℕ => ∫ ω, |sampleMean X N ω - ∫ ω', X 0 ω' ∂μ| ∂μ) =O[atTop]
      (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) := by
  refine IsBigO.of_bound (Real.sqrt (variance (X 0) μ)) ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hN
  let Y : Ω → ℝ := fun ω => sampleMean X N ω - ∫ ω', X 0 ω' ∂μ
  have hS_mem : MemLp (sampleMean X N) 2 μ := by
    rw [sampleMean_eq]
    exact (memLp_finset_sum (s := Finset.range N) (fun i _ => hX i)).const_mul _
  have hY_mem : MemLp Y 2 μ := hS_mem.sub (memLp_const _)
  have hS_int : Integrable (sampleMean X N) μ := memLp_two_integrable hS_mem
  have hY_mean : ∫ ω, Y ω ∂μ = 0 := by
    rw [show Y = fun ω => sampleMean X N ω - ∫ ω', X 0 ω' ∂μ from rfl]
    rw [integral_sub hS_int (integrable_const _),
      integral_sampleMean X (fun i => memLp_two_integrable (hX i)) hident hN]
    simp
  have hsq : ∫ ω, Y ω ^ 2 ∂μ = variance Y μ := by
    rw [variance_eq_integral hY_mem.aemeasurable]
    simp [hY_mean]
  have hmono : lpNorm Y 1 μ ≤ lpNorm Y 2 μ := by
    rw [← toReal_eLpNorm hY_mem.1, ← toReal_eLpNorm hY_mem.1]
    exact ENNReal.toReal_mono hY_mem.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num) hY_mem.1)
  have hlp : lpNorm Y 2 μ = Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num) hY_mem.1]
    rw [Real.sqrt_eq_rpow]
    have hexp : (ENNReal.toReal 2)⁻¹ = (1 / 2 : ℝ) := by norm_num
    rw [hexp]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    simp [Real.norm_eq_abs, sq_abs]
  have hvarY : variance Y μ = variance (sampleMean X N) μ :=
    variance_sub_const hS_mem.1 _
  have hvarN : variance (sampleMean X N) μ = variance (X 0) μ / N :=
    variance_sampleMean X hX hindep hident hN
  have hbound : ∫ ω, |Y ω| ∂μ ≤ Real.sqrt (variance (X 0) μ) / Real.sqrt (N : ℝ) := by
    calc
      ∫ ω, |Y ω| ∂μ = lpNorm Y 1 μ := (lpNorm_one_eq_integral_norm hY_mem.1).symm
      _ ≤ lpNorm Y 2 μ := hmono
      _ = Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := hlp
      _ = Real.sqrt (variance Y μ) := by rw [hsq]
      _ = Real.sqrt (variance (sampleMean X N) μ) := by rw [hvarY]
      _ = Real.sqrt (variance (X 0) μ / N) := by rw [hvarN]
      _ = Real.sqrt (variance (X 0) μ) / Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_div (variance_nonneg (X 0) μ)]
  have hnonneg : 0 ≤ ∫ ω, |Y ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  change ‖∫ ω, |Y ω| ∂μ‖ ≤
    Real.sqrt (variance (X 0) μ) * ‖(Real.sqrt (N : ℝ))⁻¹‖
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simpa [div_eq_mul_inv] using hbound

end HDP
