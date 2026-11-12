import Mathlib

/-! Chapter 1's Bernoulli moments and Poisson limit theorem.

The triangular Poisson limit is proved using Fourier inversion on the circle,
without assuming a general continuity theorem for characteristic functions.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace HDP

set_option backward.isDefEq.respectTransparency false

/-- Numerical realization of a Boolean Bernoulli random variable. -/
def bernoulliValue (b : Bool) : ℝ := cond b 1 0

/-- The Bernoulli law on the real line, including the endpoint parameters. -/
noncomputable def bernoulliMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure ℝ :=
  (PMF.bernoulli p hp).toMeasure.map bernoulliValue

/-- The binomial law on the real line. -/
noncomputable def binomialMeasure (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure ℝ :=
  (PMF.binomial p hp N).toMeasure.map (fun k : Fin (N + 1) ↦ (k.val : ℝ))

/-- The Poisson law on the real line; zero rate is included. -/
noncomputable def poissonMeasureReal (r : ℝ≥0) : Measure ℝ :=
  (poissonMeasure r).map (fun k : ℕ ↦ (k : ℝ))

/-- The numerical sum in a finite Bernoulli triangular row. -/
def bernoulliRowSum {Ω : Type*} (X : (N : ℕ) → Fin N → Ω → Bool)
    (N : ℕ) (ω : Ω) : ℝ := ∑ i, bernoulliValue (X N i ω)

/-- Weak convergence of the real row sums to the Poisson law, expressed using
all bounded continuous real test functions. -/
def ConvergesToPoisson {Ω : Type*} [MeasurableSpace Ω]
    (X : (N : ℕ) → Fin N → Ω → Bool) (μ : Measure Ω) (r : ℝ≥0) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun N ↦ ∫ ω, f (bernoulliRowSum X N ω) ∂μ) atTop
      (𝓝 (∫ k : ℕ, f (k : ℝ) ∂poissonMeasure r))

/-- Integration against a Bernoulli law is a two-term weighted sum. -/
theorem bernoulli_integral (p : ℝ≥0) (hp : p ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(PMF.bernoulli p hp).toMeasure =
      (1 - (p : ℝ)) * f false + (p : ℝ) * f true := by
  rw [PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply, NNReal.coe_sub hp, mul_comm, add_comm]

/-- The expectation recalled in the Bernoulli paragraph on printed page 10. -/
theorem bernoulli_expectation (p : ℝ≥0) (hp : p ≤ 1) :
    ∫ b, bernoulliValue b ∂(PMF.bernoulli p hp).toMeasure = (p : ℝ) := by
  simpa [bernoulliValue] using PMF.bernoulli_expectation hp

/-- The variance recalled in the Bernoulli paragraph on printed page 10. -/
theorem bernoulli_variance (p : ℝ≥0) (hp : p ≤ 1) :
    Var[bernoulliValue; (PMF.bernoulli p hp).toMeasure] = (p : ℝ) * (1 - (p : ℝ)) := by
  rw [variance_eq_integral (AEMeasurable.of_discrete : AEMeasurable bernoulliValue
    (PMF.bernoulli p hp).toMeasure),
    bernoulli_expectation, bernoulli_integral]
  simp only [bernoulliValue, Bool.cond_false, Bool.cond_true]
  ring

/-- Source (1.8): the Poisson mass formula, with zero rate allowed. -/
theorem poisson_mass (r : ℝ≥0) (k : ℕ) :
    poissonMeasure r {k} =
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ)) := by
  rw [poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]
  rfl

/-- The sum of squared rare-event parameters is controlled by the maximum parameter
times the sum of parameters. This is the elementary error bound needed by a
Poisson approximation argument. -/
theorem sum_sq_le_max_mul_sum {N : ℕ} (p : Fin N → ℝ≥0) :
    ∑ i, p i ^ 2 ≤ Finset.univ.sup p * ∑ i, p i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [pow_two]
  exact mul_le_mul_of_nonneg_right (Finset.le_sup hi) (zero_le _)

/-- Both hypotheses in the law of small numbers imply that the sum of squared
parameters vanishes; no probability or independence assumptions are required. -/
theorem tendsto_sum_sq_zero
    (p : (N : ℕ) → Fin N → ℝ≥0) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) :
    Tendsto (fun N ↦ ∑ i, p N i ^ 2) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun N ↦ Finset.univ.sup (p N) * ∑ i, p N i) atTop (𝓝 0) from
      by simpa using hmax.mul hsum)
    (fun _ ↦ zero_le _) (fun N ↦ sum_sq_le_max_mul_sum (p N))

/-- A uniform quadratic remainder estimate for the complex logarithm. -/
theorem norm_log_one_add_sub_le_sq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - z‖ ≤ ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)]
    linarith
  calc
    ‖Complex.log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le hz1
    _ ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring

/-- Error estimate for the logarithm of a finite triangular generating product. -/
theorem norm_sum_log_sub_le_sum_sq {N : ℕ} (p : Fin N → ℝ≥0) (z : ℂ)
    (hp : ∀ i, (p i : ℝ) * ‖z‖ ≤ 1 / 2) :
    ‖(∑ i, Complex.log (1 + (p i : ℂ) * z)) - (∑ i, (p i : ℂ)) * z‖ ≤
      (∑ i, (p i : ℝ) ^ 2) * ‖z‖ ^ 2 := by
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hn : ‖(p i : ℂ) * z‖ = (p i : ℝ) * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p i).coe_nonneg]
  have h := norm_log_one_add_sub_le_sq (z := (p i : ℂ) * z) (by rw [hn]; exact hp i)
  simpa only [hn, mul_pow] using h

/-- The analytic triangular-product limit underlying the law of small numbers.
This theorem has no probabilistic hypotheses: the generating function argument
can use it at every fixed complex value. -/
theorem tendsto_bernoulli_generating_product
    (p : (N : ℕ) → Fin N → ℝ≥0) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) (z : ℂ) :
    Tendsto (fun N ↦ ∏ i, (1 + (p N i : ℂ) * z)) atTop
      (𝓝 (Complex.exp ((r : ℂ) * z))) := by
  have hsmall : ∀ᶠ N in atTop, ∀ i, (p N i : ℝ) * ‖z‖ ≤ 1 / 2 := by
    have ht : Tendsto (fun N ↦ ((Finset.univ.sup (p N) : ℝ≥0) : ℝ) * ‖z‖)
        atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_coe.mpr hmax).mul_const ‖z‖
    filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hN i
    apply le_trans (mul_le_mul_of_nonneg_right _ (norm_nonneg z)) hN.le
    exact_mod_cast (Finset.le_sup (f := p N) (Finset.mem_univ i))
  have hsq : Tendsto (fun N ↦ (∑ i, (p N i : ℝ) ^ 2) * ‖z‖ ^ 2) atTop (𝓝 0) := by
    simpa using (NNReal.tendsto_coe.mpr (tendsto_sum_sq_zero p r hmax hsum)).mul_const
      (‖z‖ ^ 2)
  have herr : Tendsto
      (fun N ↦ (∑ i, Complex.log (1 + (p N i : ℂ) * z)) - (∑ i, (p N i : ℂ)) * z)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _ hsq
    filter_upwards [hsmall] with N hN
    exact norm_sum_log_sub_le_sum_sq (p N) z hN
  have hlinear : Tendsto (fun N ↦ (∑ i, (p N i : ℂ)) * z) atTop
      (𝓝 ((r : ℂ) * z)) := by
    simpa using ((Complex.continuous_ofReal.tendsto (r : ℝ)).comp
      (NNReal.tendsto_coe.mpr hsum)).mul_const z
  have hlog : Tendsto (fun N ↦ ∑ i, Complex.log (1 + (p N i : ℂ) * z)) atTop
      (𝓝 ((r : ℂ) * z)) := by
    simpa using herr.add hlinear
  apply (Complex.continuous_exp.tendsto _ |>.comp hlog).congr'
  filter_upwards [hsmall] with N hN
  dsimp only [Function.comp_def]
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  apply Complex.exp_log
  intro heq
  have hn : ‖(p N i : ℂ) * z‖ = (p N i : ℝ) * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (p N i).coe_nonneg]
  have he : (p N i : ℂ) * z = -1 := by linear_combination heq
  have hnorm : (p N i : ℝ) * ‖z‖ = 1 := by simpa [he] using hn.symm
  linarith [hN i]

/-- The probability-of-no-events product converges to the Poisson zero mass. -/
theorem tendsto_product_one_sub
    (p : (N : ℕ) → Fin N → ℝ≥0) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) :
    Tendsto (fun N ↦ ∏ i, (1 - (p N i : ℝ))) atTop (𝓝 (Real.exp (-(r : ℝ)))) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_bernoulli_generating_product p r hmax hsum (-1))
  have heq (N : ℕ) : (∏ i, (1 + (p N i : ℂ) * (-1))).re =
      ∏ i, (1 - (p N i : ℝ)) := by
    have he : (∏ i, (1 + (p N i : ℂ) * (-1))) =
        ((∏ i, (1 - (p N i : ℝ)) : ℝ) : ℂ) := by push_cast; congr 1; funext i; ring
    rw [he]
    rfl
  change Tendsto (fun N ↦ (∏ i, (1 + (p N i : ℂ) * (-1))).re) atTop
    (𝓝 (Complex.exp ((r : ℂ) * (-1))).re) at h
  simp only [heq] at h
  simpa [Complex.exp_re] using h

/-- Each Bernoulli generating factor is bounded by one on the unit circle. -/
theorem norm_bernoulli_factor_le_one (p : ℝ≥0) (hp : p ≤ 1) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖1 + (p : ℂ) * (w - 1)‖ ≤ 1 := by
  have hp' : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  calc
    ‖1 + (p : ℂ) * (w - 1)‖ = ‖((1 - (p : ℝ) : ℝ) : ℂ) + (p : ℂ) * w‖ := by
      congr 1
      push_cast
      ring
    _ ≤ ‖((1 - (p : ℝ) : ℝ) : ℂ)‖ + ‖(p : ℂ) * w‖ := norm_add_le _ _
    _ = 1 := by
      rw [norm_mul, hw, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
        abs_of_nonneg p.coe_nonneg]
      ring

/-- Fourier coefficients of the triangular generating functions converge.
Dominated convergence is available because every generating factor is bounded
by one on the unit circle. This supplies the analytic inversion step without
appealing to a general continuity theorem for characteristic functions. -/
theorem tendsto_fourierCoeff_bernoulli_product
    (p : (N : ℕ) → Fin N → ℝ≥0) (hp : ∀ N i, p N i ≤ 1) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) (k : ℤ) :
    Tendsto (fun N ↦ fourierCoeff (T := 1)
      (fun t ↦ ∏ i, (1 + (p N i : ℂ) * (fourier 1 t - 1))) k) atTop
      (𝓝 (fourierCoeff (T := 1)
        (fun t ↦ Complex.exp ((r : ℂ) * (fourier 1 t - 1))) k)) := by
  simp only [fourierCoeff, smul_eq_mul]
  apply tendsto_integral_filter_of_norm_le_const
  · apply Eventually.of_forall
    intro N
    exact (show Continuous (fun t : AddCircle (1 : ℝ) ↦
      fourier (-k) t * ∏ i, (1 + (p N i : ℂ) * (fourier 1 t - 1))) by
        fun_prop).aestronglyMeasurable
  · refine ⟨1, Eventually.of_forall (fun N ↦ ae_of_all _ (fun t ↦ ?_))⟩
    rw [norm_mul]
    have hf (j : ℤ) : ‖fourier j t‖ = 1 := Circle.norm_coe _
    rw [hf, one_mul]
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
    intro i _
    exact norm_bernoulli_factor_le_one (p N i) (hp N i) (fourier 1 t) (hf 1)
  · apply ae_of_all
    intro t
    exact tendsto_const_nhds.mul (tendsto_bernoulli_generating_product p r hmax hsum
      (fourier 1 t - 1))

/-- Fourier inversion for an absolutely summable series supported on nonnegative
integer frequencies. This applies directly to a probability mass function. -/
theorem fourierCoeff_tsum_nat (a : ℕ → ℂ) (ha : Summable (fun n ↦ ‖a n‖)) (k : ℕ) :
    fourierCoeff (T := 1) (fun t ↦ ∑' n : ℕ, a n * fourier (n : ℤ) t) (k : ℤ) = a k := by
  have hf (j : ℤ) (t : AddCircle (1 : ℝ)) : ‖fourier j t‖ = 1 := Circle.norm_coe _
  have hnorm (n : ℕ) (t : AddCircle (1 : ℝ)) :
      ‖fourier (-(k : ℤ)) t * (a n * fourier (n : ℤ) t)‖ = ‖a n‖ := by
    simp only [norm_mul, hf, mul_one, one_mul]
  have hint (n : ℕ) : Integrable
      (fun t : AddCircle (1 : ℝ) ↦ fourier (-(k : ℤ)) t * (a n * fourier (n : ℤ) t))
      AddCircle.haarAddCircle := by
    refine Integrable.of_bound (by fun_prop) ‖a n‖ (ae_of_all _ (fun t ↦ ?_))
    exact (hnorm n t).le
  have hsum : Summable (fun n : ℕ ↦ ∫ t : AddCircle (1 : ℝ),
      ‖fourier (-(k : ℤ)) t * (a n * fourier (n : ℤ) t)‖ ∂AddCircle.haarAddCircle) := by
    simpa only [hnorm, integral_const, probReal_univ, smul_eq_mul, one_mul] using ha
  have hcoeff (n : ℕ) : (∫ t : AddCircle (1 : ℝ),
      fourier (-(k : ℤ)) t * (a n * fourier (n : ℤ) t) ∂AddCircle.haarAddCircle) =
      if n = k then a k else 0 := by
    change fourierCoeff (fun t : AddCircle (1 : ℝ) ↦ a n * fourier (n : ℤ) t) (k : ℤ) = _
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
    by_cases h : n = k
    · subst n
      simp
    · have h' : (k : ℤ) ≠ (n : ℤ) := by exact_mod_cast Ne.symm h
      simp [h, h']
  unfold fourierCoeff
  simp only [smul_eq_mul, ← tsum_mul_left]
  trans ∑' n : ℕ, ∫ t : AddCircle (1 : ℝ),
    fourier (-(k : ℤ)) t * (a n * fourier (n : ℤ) t) ∂AddCircle.haarAddCircle
  · exact (integral_tsum_of_summable_integral_norm hint hsum).symm
  simp only [hcoeff]
  exact tsum_ite_eq k (fun _ ↦ a k)

/-- Powers of the first circle character are the nonnegative-frequency characters. -/
theorem fourier_one_pow (n : ℕ) (t : AddCircle (1 : ℝ)) :
    fourier 1 t ^ n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]

/-- The Fourier series of the Poisson generating function is its mass function. -/
theorem poisson_fourier_hasSum (r : ℝ≥0) (t : AddCircle (1 : ℝ)) :
    HasSum (fun n : ℕ ↦ (poissonPMFReal r n : ℂ) * fourier (n : ℤ) t)
      (Complex.exp ((r : ℂ) * (fourier 1 t - 1))) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * fourier 1 t)).mul_left
    (Complex.exp (-(r : ℂ)))
  rw [← Complex.exp_eq_exp_ℂ] at hs
  convert hs using 1
  · ext n
    simp only [poissonPMFReal, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_natCast, mul_pow, fourier_one_pow]
    ring
  · rw [← Complex.exp_add]
    congr 1
    ring

/-- Fourier inversion identifies the limiting coefficient with the Poisson mass. -/
theorem fourierCoeff_poisson (r : ℝ≥0) (k : ℕ) :
    fourierCoeff (T := 1) (fun t ↦ Complex.exp ((r : ℂ) * (fourier 1 t - 1))) (k : ℤ) =
      (poissonPMFReal r k : ℂ) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖(poissonPMFReal r n : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg poissonPMFReal_nonneg]
      using (poissonPMFRealSum r).summable
  convert fourierCoeff_tsum_nat (fun n ↦ (poissonPMFReal r n : ℂ)) hnorm k using 1
  congr 1
  ext t
  exact (poisson_fourier_hasSum r t).tsum_eq.symm

/-- Inversion of the Fourier transform of a probability measure on the naturals. -/
theorem fourierCoeff_natMeasure (ν : Measure ℕ) [IsProbabilityMeasure ν] (k : ℕ) :
    fourierCoeff (T := 1) (fun t ↦ ∫ n : ℕ, fourier (n : ℤ) t ∂ν) (k : ℤ) =
      ((ν {k}).toReal : ℂ) := by
  let q := ν.toPMF
  have hn : Summable (fun n : ℕ ↦ ‖((q n).toReal : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      using ENNReal.summable_toReal q.tsum_coe_ne_top
  have hi (t : AddCircle (1 : ℝ)) : Integrable (fun n : ℕ ↦ fourier (n : ℤ) t) q.toMeasure := by
    refine Integrable.of_bound AEStronglyMeasurable.of_discrete 1 (ae_of_all _ (fun n ↦ ?_))
    exact (Circle.norm_coe _).le
  have hs (t : AddCircle (1 : ℝ)) :
      (∫ n : ℕ, fourier (n : ℤ) t ∂ν) = ∑' n : ℕ, ((q n).toReal : ℂ) * fourier (n : ℤ) t := by
    rw [← Measure.toPMF_toMeasure ν, PMF.integral_eq_tsum _ _ (hi t)]
    simp only [q, Complex.real_smul]
  convert fourierCoeff_tsum_nat (fun n ↦ ((q n).toReal : ℂ)) hn k using 1
  congr 1
  ext t
  exact hs t

/-- A natural-valued version of the Bernoulli row sum used for discrete inversion. -/
def bernoulliRowCount {Ω : Type*} (X : (N : ℕ) → Fin N → Ω → Bool)
    (N : ℕ) (ω : Ω) : ℕ := ∑ i, (X N i ω).toNat

theorem bernoulliRowSum_eq_cast_count {Ω : Type*}
    (X : (N : ℕ) → Fin N → Ω → Bool) (N : ℕ) (ω : Ω) :
    bernoulliRowSum X N ω = (bernoulliRowCount X N ω : ℝ) := by
  simp only [bernoulliRowSum, bernoulliRowCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases X N i ω <;> simp [bernoulliValue]

/-- Characters turn a finite sum of natural values into a product. -/
theorem fourier_nat_sum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (t : AddCircle (1 : ℝ)) :
    fourier ((∑ i ∈ s, n i : ℕ) : ℤ) t = ∏ i ∈ s, fourier (n i : ℤ) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, Nat.cast_add, fourier_add, ih]

/-- Independence identifies the Fourier transform of each row with its generating product. -/
theorem bernoulliRowCount_fourier
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (N : ℕ) → Fin N → Ω → Bool)
    (p : (N : ℕ) → Fin N → ℝ≥0) (hp : ∀ N i, p N i ≤ 1)
    (hLaw : ∀ N i, HasLaw (X N i) (PMF.bernoulli (p N i) (hp N i)).toMeasure μ)
    (hIndep : ∀ N, iIndepFun (X N) μ) (N : ℕ) (t : AddCircle (1 : ℝ)) :
    (∫ ω, fourier (bernoulliRowCount X N ω : ℤ) t ∂μ) =
      ∏ i, (1 + (p N i : ℂ) * (fourier 1 t - 1)) := by
  simp only [bernoulliRowCount, fourier_nat_sum]
  trans ∏ i, ∫ ω, fourier ((X N i ω).toNat : ℤ) t ∂μ
  · exact (hIndep N).integral_fun_prod_comp
      (f := fun (_ : Fin N) (b : Bool) ↦ fourier (b.toNat : ℤ) t)
      (fun i ↦ (hLaw N i).aemeasurable) (fun _ ↦ AEStronglyMeasurable.of_discrete)
  apply Finset.prod_congr rfl
  intro i _
  have he := (hLaw N i).integral_comp (f := fun b : Bool ↦ fourier (b.toNat : ℤ) t)
    AEStronglyMeasurable.of_discrete
  simp only [Function.comp_def] at he
  rw [he, PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply, NNReal.coe_sub (hp N i), Complex.real_smul]
  ring

/-- On the discrete natural numbers, convergence of all singleton probabilities
already implies weak convergence. The singleton sets form a neighbourhood
π-system, so the portmanteau convergence criterion applies. -/
theorem tendsto_probabilityMeasure_nat_of_singletons
    (νs : ℕ → ProbabilityMeasure ℕ) (ν : ProbabilityMeasure ℕ)
    (h : ∀ k : ℕ, Tendsto (fun N ↦ (νs N {k} : ℝ)) atTop (𝓝 (ν {k} : ℝ))) :
    Tendsto νs atTop (𝓝 ν) := by
  let S : Set (Set ℕ) := Set.range (fun k : ℕ ↦ ({k} : Set ℕ))
  have hS : IsPiSystem S := by
    rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ ⟨x, hx⟩
    have hi : x = i := Set.mem_singleton_iff.mp hx.1
    have hj : x = j := Set.mem_singleton_iff.mp hx.2
    have hij : i = j := hi.symm.trans hj
    exact ⟨i, by simp only [← hij, Set.inter_self]⟩
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨k, rfl⟩
    exact measurableSet_singleton k
  · intro u _ x hx
    refine ⟨{x}, ⟨x, rfl⟩, ?_, Set.singleton_subset_iff.mpr hx⟩
    exact (isOpen_discrete _).mem_nhds (Set.mem_singleton x)
  · rintro s ⟨k, rfl⟩
    exact NNReal.tendsto_coe.mp (h k)

theorem aemeasurable_bernoulliRowCount
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : (N : ℕ) → Fin N → Ω → Bool) (N : ℕ)
    (hX : ∀ i, AEMeasurable (X N i) μ) :
    AEMeasurable (bernoulliRowCount X N) μ := by
  apply Finset.aemeasurable_fun_sum
  intro i _
  exact (measurable_of_finite Bool.toNat).comp_aemeasurable (hX i)

/-- The law of small numbers yields convergence of every individual point mass.
The proof uses Fourier inversion on the unit circle and dominated convergence. -/
theorem bernoulliRowCount_singleton_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (N : ℕ) → Fin N → Ω → Bool)
    (p : (N : ℕ) → Fin N → ℝ≥0) (hp : ∀ N i, p N i ≤ 1)
    (hLaw : ∀ N i, HasLaw (X N i) (PMF.bernoulli (p N i) (hp N i)).toMeasure μ)
    (hIndep : ∀ N, iIndepFun (X N) μ) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) (k : ℕ) :
    Tendsto (fun N ↦ ((μ.map (bernoulliRowCount X N)) {k}).toReal) atTop
      (𝓝 (poissonPMFReal r k)) := by
  have hm N := aemeasurable_bernoulliRowCount X N (fun i ↦ (hLaw N i).aemeasurable)
  have heq N : fourierCoeff (T := 1)
      (fun t ↦ ∏ i, (1 + (p N i : ℂ) * (fourier 1 t - 1))) (k : ℤ) =
        (((μ.map (bernoulliRowCount X N)) {k}).toReal : ℂ) := by
    letI : IsProbabilityMeasure (μ.map (bernoulliRowCount X N)) :=
      Measure.isProbabilityMeasure_map (hm N)
    rw [← fourierCoeff_natMeasure (μ.map (bernoulliRowCount X N)) k]
    congr 1
    ext t
    rw [integral_map (hm N) AEStronglyMeasurable.of_discrete]
    exact (bernoulliRowCount_fourier μ X p hp hLaw hIndep N t).symm
  have hc := tendsto_fourierCoeff_bernoulli_product p hp r hmax hsum (k : ℤ)
  simp only [heq, fourierCoeff_poisson] at hc
  exact tendsto_ofReal_iff.mp hc

/-- Theorem 1.3.4 (Poisson Limit Theorem), including zero limiting rate.
Independence is imposed separately inside each finite triangular row. -/
theorem poisson_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (N : ℕ) → Fin N → Ω → Bool)
    (p : (N : ℕ) → Fin N → ℝ≥0) (hp : ∀ N i, p N i ≤ 1)
    (hLaw : ∀ N i, HasLaw (X N i) (PMF.bernoulli (p N i) (hp N i)).toMeasure μ)
    (hIndep : ∀ N, iIndepFun (X N) μ) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) :
    ConvergesToPoisson X μ r := by
  have hm N := aemeasurable_bernoulliRowCount X N (fun i ↦ (hLaw N i).aemeasurable)
  let νs : ℕ → ProbabilityMeasure ℕ := fun N ↦
    ⟨μ.map (bernoulliRowCount X N), Measure.isProbabilityMeasure_map (hm N)⟩
  let ν : ProbabilityMeasure ℕ := ⟨poissonMeasure r, inferInstance⟩
  have hw : Tendsto νs atTop (𝓝 ν) := by
    apply tendsto_probabilityMeasure_nat_of_singletons
    intro k
    have h := bernoulliRowCount_singleton_limit μ X p hp hLaw hIndep r hmax hsum k
    change Tendsto (fun N ↦ ((μ.map (bernoulliRowCount X N)) {k}).toReal) atTop
      (𝓝 ((poissonMeasure r) {k}).toReal)
    rw [poisson_mass, ENNReal.toReal_ofReal (by positivity)]
    exact h
  intro f
  let g : BoundedContinuousFunction ℕ ℝ :=
    f.compContinuous ⟨(fun k : ℕ ↦ (k : ℝ)), continuous_of_discreteTopology⟩
  have hi := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw g
  change Tendsto (fun N ↦ ∫ ω, f (bernoulliRowSum X N ω) ∂μ) atTop
    (𝓝 (∫ k : ℕ, f (k : ℝ) ∂poissonMeasure r))
  convert hi using 1
  · ext N
    change (∫ ω, f (bernoulliRowSum X N ω) ∂μ) =
      ∫ k : ℕ, f (k : ℝ) ∂μ.map (bernoulliRowCount X N)
    rw [integral_map (hm N) (by fun_prop)]
    simp only [bernoulliRowSum_eq_cast_count]

/-- The binomial generating function on the unit circle. -/
theorem binomial_fourier_integral (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (t : AddCircle (1 : ℝ)) :
    (∫ j : Fin (N + 1), fourier (j.val : ℤ) t ∂(PMF.binomial p hp N).toMeasure) =
      (1 + (p : ℂ) * (fourier 1 t - 1)) ^ N := by
  rw [PMF.integral_eq_sum]
  have hw (j : Fin (N + 1)) : ((PMF.binomial p hp N j).toReal : ℂ) =
      (p : ℂ) ^ j.val * (1 - (p : ℂ)) ^ (N - j.val) * (N.choose j.val : ℂ) := by
    rw [PMF.binomial_apply]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.coe_toReal, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp) (by simp)]
    simp only [ENNReal.toReal_one, ENNReal.coe_toReal, Complex.ofReal_sub, Complex.ofReal_one,
      Fin.val_last]
  simp only [Complex.real_smul, hw, ← fourier_one_pow]
  have he : (1 + (p : ℂ) * (fourier 1 t - 1)) =
      (p : ℂ) * fourier 1 t + (1 - (p : ℂ)) := by ring
  rw [he, add_pow, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < N + 1 := Finset.mem_range.mp hj
  simp only [dif_pos hj']
  rw [mul_pow]
  ring

/-- A fixed finite independent Bernoulli family has the expected Fourier product. -/
theorem independent_bernoulli_count_fourier
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (X : Fin N → Ω → Bool) (p : ℝ≥0) (hp : p ≤ 1)
    (hLaw : ∀ i, HasLaw (X i) (PMF.bernoulli p hp).toMeasure μ)
    (hIndep : iIndepFun X μ) (t : AddCircle (1 : ℝ)) :
    (∫ ω, fourier ((∑ i, (X i ω).toNat : ℕ) : ℤ) t ∂μ) =
      (1 + (p : ℂ) * (fourier 1 t - 1)) ^ N := by
  simp only [fourier_nat_sum]
  trans ∏ i, ∫ ω, fourier ((X i ω).toNat : ℤ) t ∂μ
  · exact hIndep.integral_fun_prod_comp
      (f := fun (_ : Fin N) (b : Bool) ↦ fourier (b.toNat : ℤ) t)
      (fun i ↦ (hLaw i).aemeasurable) (fun _ ↦ AEStronglyMeasurable.of_discrete)
  trans ∏ _i : Fin N, (1 + (p : ℂ) * (fourier 1 t - 1))
  · apply Finset.prod_congr rfl
    intro i _
    have he := (hLaw i).integral_comp (f := fun b : Bool ↦ fourier (b.toNat : ℤ) t)
      AEStronglyMeasurable.of_discrete
    simp only [Function.comp_def] at he
    rw [he, PMF.integral_eq_sum]
    simp [PMF.bernoulli_apply, NNReal.coe_sub hp, Complex.real_smul]
    ring
  simp

theorem bernoulliMeasure_one (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp {1} = (p : ℝ≥0∞) := by
  rw [bernoulliMeasure, Measure.map_apply (measurable_of_finite bernoulliValue)
    (measurableSet_singleton 1)]
  have he : bernoulliValue ⁻¹' ({1} : Set ℝ) = {true} := by
    ext b
    cases b <;> simp [bernoulliValue]
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true)]
  simp [PMF.bernoulli_apply]

theorem bernoulliMeasure_zero (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp {0} = ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  rw [bernoulliMeasure, Measure.map_apply (measurable_of_finite bernoulliValue)
    (measurableSet_singleton 0)]
  have he : bernoulliValue ⁻¹' ({0} : Set ℝ) = {false} := by
    ext b
    cases b <;> simp [bernoulliValue]
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton false)]
  simp [PMF.bernoulli_apply, ENNReal.coe_sub]

theorem bernoulliMeasure_support (p : ℝ≥0) (hp : p ≤ 1) :
    ∀ᵐ x ∂bernoulliMeasure p hp, x = 0 ∨ x = 1 := by
  apply (ae_map_iff (measurable_of_finite bernoulliValue).aemeasurable
    (by measurability)).mpr
  apply ae_of_all
  intro b
  cases b <;> simp [bernoulliValue]

theorem hasLaw_bernoulli_expectation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (p : ℝ≥0) (hp : p ≤ 1)
    (hY : HasLaw Y (bernoulliMeasure p hp) μ) : ∫ ω, Y ω ∂μ = (p : ℝ) := by
  rw [hY.integral_eq]
  exact (integral_map (measurable_of_finite bernoulliValue).aemeasurable
    aestronglyMeasurable_id).trans (bernoulli_expectation p hp)

theorem hasLaw_bernoulli_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (p : ℝ≥0) (hp : p ≤ 1)
    (hY : HasLaw Y (bernoulliMeasure p hp) μ) :
    Var[Y; μ] = (p : ℝ) * (1 - (p : ℝ)) := by
  rw [hY.variance_eq, bernoulliMeasure,
    variance_map aemeasurable_id (measurable_of_finite bernoulliValue).aemeasurable]
  exact bernoulli_variance p hp

/-- A real random variable with a Bernoulli law belongs to L². -/
theorem hasLaw_bernoulli_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (p : ℝ≥0) (hp : p ≤ 1)
    (hY : HasLaw Y (bernoulliMeasure p hp) μ) : MemLp Y 2 μ := by
  have hr : MemLp (id : ℝ → ℝ) 2 (bernoulliMeasure p hp) := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_of_finite bernoulliValue).aemeasurable).mpr
    exact MemLp.of_discrete
  rw [← hY.map_eq] at hr
  exact (memLp_map_measure_iff aestronglyMeasurable_id hY.aemeasurable).mp hr

theorem bernoulliRowSum_expectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (N : ℕ) → Fin N → Ω → Bool)
    (p : (N : ℕ) → Fin N → ℝ≥0) (hp : ∀ N i, p N i ≤ 1)
    (hLaw : ∀ N i, HasLaw (X N i) (PMF.bernoulli (p N i) (hp N i)).toMeasure μ)
    (N : ℕ) : ∫ ω, bernoulliRowSum X N ω ∂μ = ∑ i, (p N i : ℝ) := by
  have hi i : Integrable (fun ω ↦ bernoulliValue (X N i ω)) μ := by
    change Integrable (bernoulliValue ∘ X N i) μ
    apply (integrable_map_measure (g := bernoulliValue) AEStronglyMeasurable.of_discrete
      (hLaw N i).aemeasurable).mp
    rw [(hLaw N i).map_eq]
    exact Integrable.of_finite
  change (∫ ω, ∑ i, bernoulliValue (X N i ω) ∂μ) = _
  rw [integral_finset_sum _ (fun i _ ↦ hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have he := (hLaw N i).integral_comp (f := bernoulliValue) AEStronglyMeasurable.of_discrete
  simpa only [Function.comp_def, bernoulli_expectation] using he

theorem poissonMeasureReal_mass (r : ℝ≥0) (k : ℕ) :
    poissonMeasureReal r {(k : ℝ)} =
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ)) := by
  rw [poissonMeasureReal, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have he : (fun n : ℕ ↦ (n : ℝ)) ⁻¹' {(k : ℝ)} = {k} := by
    ext n
    simp
  rw [he, poisson_mass]

theorem poissonMeasureReal_support (r : ℝ≥0) :
    ∀ᵐ x ∂poissonMeasureReal r, ∃ k : ℕ, x = (k : ℝ) := by
  apply (ae_map_iff (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).aemeasurable
    (by measurability)).mpr
  exact ae_of_all _ (fun n ↦ ⟨n, rfl⟩)

/-- Fourier transforms determine probability measures on the naturals. -/
theorem natMeasure_eq_of_fourier (ν₁ ν₂ : Measure ℕ)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ t : AddCircle (1 : ℝ),
      (∫ n : ℕ, fourier (n : ℤ) t ∂ν₁) = ∫ n : ℕ, fourier (n : ℤ) t ∂ν₂) :
    ν₁ = ν₂ := by
  apply ext_iff_measureReal_singleton.mpr
  intro k
  apply Complex.ofReal_injective
  change ((ν₁ {k}).toReal : ℂ) = ((ν₂ {k}).toReal : ℂ)
  rw [← fourierCoeff_natMeasure ν₁ k, ← fourierCoeff_natMeasure ν₂ k]
  congr 1
  ext t
  exact h t

/-- The binomial paragraph: the numerical sum of independent equally parameterized
Bernoulli variables has the binomial law. -/
theorem binomial_sum_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (X : Fin N → Ω → Bool) (p : ℝ≥0) (hp : p ≤ 1)
    (hLaw : ∀ i, HasLaw (X i) (PMF.bernoulli p hp).toMeasure μ)
    (hIndep : iIndepFun X μ) :
    HasLaw (fun ω ↦ ∑ i, bernoulliValue (X i ω)) (binomialMeasure N p hp) μ := by
  let count : Ω → ℕ := fun ω ↦ ∑ i, (X i ω).toNat
  have mc : AEMeasurable count μ := by
    apply Finset.aemeasurable_fun_sum
    intro i _
    exact (measurable_of_finite Bool.toNat).comp_aemeasurable (hLaw i).aemeasurable
  let νb : Measure ℕ := (PMF.binomial p hp N).toMeasure.map (fun j : Fin (N + 1) ↦ j.val)
  letI : IsProbabilityMeasure (μ.map count) := Measure.isProbabilityMeasure_map mc
  letI : IsProbabilityMeasure νb := Measure.isProbabilityMeasure_map
    (measurable_of_finite (fun j : Fin (N + 1) ↦ j.val)).aemeasurable
  have heq : μ.map count = νb := by
    apply natMeasure_eq_of_fourier
    intro t
    change (∫ n : ℕ, fourier (n : ℤ) t ∂μ.map count) =
      ∫ n : ℕ, fourier (n : ℤ) t ∂(PMF.binomial p hp N).toMeasure.map (fun j ↦ j.val)
    rw [integral_map mc AEStronglyMeasurable.of_discrete,
      integral_map (measurable_of_finite (fun j : Fin (N + 1) ↦ j.val)).aemeasurable
        AEStronglyMeasurable.of_discrete]
    exact (independent_bernoulli_count_fourier μ N X p hp hLaw hIndep t).trans
      (binomial_fourier_integral N p hp t).symm
  have hc : HasLaw count νb μ := ⟨mc, heq⟩
  have hcast : HasLaw (fun n : ℕ ↦ (n : ℝ)) (binomialMeasure N p hp) νb := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    dsimp only [νb, binomialMeasure]
    rw [Measure.map_map (measurable_of_countable (fun n : ℕ ↦ (n : ℝ)))
      (measurable_of_finite (fun j : Fin (N + 1) ↦ j.val))]
    rfl
  apply (hcast.comp hc).congr
  apply ae_of_all
  intro ω
  simp only [Function.comp_def, count, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases X i ω <;> simp [bernoulliValue]

/-- Measurable Boolean recoding of the real Bernoulli support. -/
noncomputable def realToBernoulli (x : ℝ) : Bool := by
  classical
  exact decide (x = 1)

@[fun_prop]
theorem measurable_realToBernoulli : Measurable realToBernoulli := by
  apply measurable_to_bool
  have he : realToBernoulli ⁻¹' {true} = ({1} : Set ℝ) := by
    ext x
    simp [realToBernoulli]
  rw [he]
  exact measurableSet_singleton 1

/-- Recoding a Bernoulli real law recovers its Boolean law exactly. -/
theorem realToBernoulli_hasLaw (p : ℝ≥0) (hp : p ≤ 1) :
    HasLaw realToBernoulli (PMF.bernoulli p hp).toMeasure (bernoulliMeasure p hp) := by
  refine ⟨measurable_realToBernoulli.aemeasurable, ?_⟩
  rw [bernoulliMeasure, Measure.map_map measurable_realToBernoulli
    (measurable_of_finite bernoulliValue)]
  have he : realToBernoulli ∘ bernoulliValue = id := by
    ext b
    cases b <;> simp [bernoulliValue, realToBernoulli]
  rw [he, Measure.map_id]

/-- Numerical reconstruction under any real Bernoulli law. -/
theorem hasLaw_bernoulli_recode_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (p : ℝ≥0) (hp : p ≤ 1) (hY : HasLaw Y (bernoulliMeasure p hp) μ) :
    (fun ω ↦ bernoulliValue (realToBernoulli (Y ω))) =ᵐ[μ] Y := by
  have hs : ∀ᵐ ω ∂μ, Y ω = 0 ∨ Y ω = 1 :=
    (hY.ae_iff (by measurability)).mpr (bernoulliMeasure_support p hp)
  filter_upwards [hs] with ω hω
  rcases hω with hω | hω <;> rw [hω] <;> simp [realToBernoulli, bernoulliValue]

/-- Theorem 1.3.4 for the source's actual real-valued triangular array.
The Boolean representation is transported using almost-everywhere reconstruction. -/
theorem poisson_limit_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (N : ℕ) → Fin N → Ω → ℝ)
    (p : (N : ℕ) → Fin N → ℝ≥0) (hp : ∀ N i, p N i ≤ 1)
    (hLaw : ∀ N i, HasLaw (X N i) (bernoulliMeasure (p N i) (hp N i)) μ)
    (hIndep : ∀ N, iIndepFun (X N) μ) (r : ℝ≥0)
    (hmax : Tendsto (fun N ↦ Finset.univ.sup (p N)) atTop (𝓝 0))
    (hsum : Tendsto (fun N ↦ ∑ i, p N i) atTop (𝓝 r)) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N ↦ ∫ ω, f (∑ i, X N i ω) ∂μ) atTop
        (𝓝 (∫ k : ℕ, f (k : ℝ) ∂poissonMeasure r)) := by
  let B : (N : ℕ) → Fin N → Ω → Bool := fun N i ↦ realToBernoulli ∘ X N i
  have hBLaw N i : HasLaw (B N i) (PMF.bernoulli (p N i) (hp N i)).toMeasure μ :=
    (realToBernoulli_hasLaw (p N i) (hp N i)).comp (hLaw N i)
  have hBInd N : iIndepFun (B N) μ :=
    (hIndep N).comp (fun _ ↦ realToBernoulli) (fun _ ↦ measurable_realToBernoulli)
  have heq N : bernoulliRowSum B N =ᵐ[μ] (fun ω ↦ ∑ i, X N i ω) := by
    have ha : ∀ᵐ ω ∂μ, ∀ i : Fin N,
        bernoulliValue (realToBernoulli (X N i ω)) = X N i ω :=
      ae_all_iff.mpr (fun i ↦ hasLaw_bernoulli_recode_ae (p N i) (hp N i) (hLaw N i))
    filter_upwards [ha] with ω hω
    exact Finset.sum_congr rfl (fun i _ ↦ hω i)
  intro f
  exact (poisson_limit μ B p hp hBLaw hBInd r hmax hsum f).congr'
    (Eventually.of_forall (fun N ↦ integral_congr_ae ((heq N).fun_comp f)))

end HDP
