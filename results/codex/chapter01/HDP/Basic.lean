import Mathlib

/-! Basic quantities and norm inequalities, supplied Chapter 1, printed pp. 5–7.

Real-valued finite quantities carry their integrability hypotheses. Extended
nonnegative quantities use `ENNReal`; `Lp` is Mathlib's a.e. quotient.
The source's p=0 endpoint is corrected to p>0. Arbitrary noninteger raw
moments of signed variables are not assigned a negative-base convention.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace

noncomputable section
namespace HDP
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

def absoluteMoment (X : Ω → ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂P

def extendedMGF (X : Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P

def nonnegativeRawMoment (X : Ω → ℝ≥0) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((X ω : ℝ) ^ p) ∂P

def extendedVariance (X : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((X ω - ∫ a, X a ∂P)^2) ∂P

def signedExtendedIntegral (f : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (f ω) ∂P) : EReal) -
  ((∫⁻ ω, ENNReal.ofReal (-f ω) ∂P) : EReal)

/-- Signed integer moments may diverge, and are undefined when both parts diverge.
No noninteger negative-base convention is selected by this definition. -/
def signedNaturalMoment (X : Ω → ℝ) (n : ℕ) : Option EReal :=
  if (∫⁻ ω, ENNReal.ofReal (X ω ^ n) ∂P) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal (-(X ω ^ n)) ∂P) = ∞ then none
  else some (signedExtendedIntegral P (fun ω => X ω ^ n))

theorem variance_formula [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) :
    variance X P = ∫ ω, (X ω - ∫ a, X a ∂P)^2 ∂P :=
  variance_eq_integral hX.aemeasurable

theorem mgf_formula (X : Ω → ℝ) (t : ℝ)
    (_h : Integrable (fun ω => Real.exp (t * X ω)) P) :
    mgf X P t = ∫ ω, Real.exp (t * X ω) ∂P := rfl

theorem natural_moment_formula (X : Ω → ℝ) (n : ℕ)
    (_h : Integrable (fun ω => X ω ^ n) P) :
    moment X n P = ∫ ω, X ω ^ n ∂P := rfl

theorem nonnegative_moment_formula (X : Ω → ℝ≥0) (p : ℝ) :
    nonnegativeRawMoment P X p = absoluteMoment P (fun ω => (X ω : ℝ)) p := by
  simp [nonnegativeRawMoment, absoluteMoment]

theorem extended_variance_formula [IsProbabilityMeasure P] (X : Ω → ℝ)
    (_hX : Integrable X P) :
    extendedVariance P X = ∫⁻ ω, ENNReal.ofReal ((X ω - ∫ a, X a ∂P)^2) ∂P := rfl

theorem mgf_finite_bridge (X : Ω → ℝ) (t : ℝ)
    (h : Integrable (fun ω => Real.exp (t * X ω)) P) :
    ENNReal.ofReal (mgf X P t) = extendedMGF P X t := by
  exact ofReal_integral_eq_lintegral_ofReal h (ae_of_all _ fun _ => (Real.exp_pos _).le)

theorem extended_mgf_finite_iff (X : Ω → ℝ) (hX : AEMeasurable X P) (t : ℝ) :
    extendedMGF P X t < ∞ ↔ Integrable (fun ω => Real.exp (t * X ω)) P := by
  have hm : AEStronglyMeasurable (fun ω => Real.exp (t * X ω)) P :=
    (hX.const_mul t).exp.aestronglyMeasurable
  have hn : 0 ≤ᵐ[P] (fun ω => Real.exp (t * X ω)) :=
    ae_of_all _ fun _ => (Real.exp_pos _).le
  exact ⟨fun h => ⟨hm, (hasFiniteIntegral_iff_ofReal hn).2 h⟩,
    fun h => (hasFiniteIntegral_iff_ofReal hn).1 h.2⟩

theorem extended_lp_formula (X : Ω → ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm X p P = (∫⁻ ω, ‖X ω‖ₑ ^ p.toReal ∂P) ^ (1 / p.toReal) :=
  eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt

theorem finite_lp_formula (X : Ω → ℝ) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hX : MemLp X p P) :
    lpNorm X p P = (∫ ω, |X ω| ^ p.toReal ∂P) ^ p.toReal⁻¹ := by
  simpa only [Real.norm_eq_abs] using
    lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hX.aestronglyMeasurable

theorem linfty_formula (X : Ω → ℝ) :
    eLpNorm X ∞ P = essSup (fun ω => ‖X ω‖ₑ) P := rfl

theorem lp_complete (p : ℝ≥0∞) [Fact (1 ≤ p)] : CompleteSpace (Lp ℝ p P) :=
  inferInstance

theorem lp_triangle {p : ℝ≥0∞} [Fact (1 ≤ p)] (X Y : Lp ℝ p P) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le X Y

theorem l2_inner_formula (X Y : Lp ℝ 2 P) :
    ⟪X, Y⟫_ℝ = ∫ ω, X ω * Y ω ∂P := by
  rw [L2.inner_def (𝕜 := ℝ)]
  apply integral_congr_ae
  filter_upwards [] with ω
  change Y ω * X ω = X ω * Y ω
  ring

theorem l2_norm_formula (X : Lp ℝ 2 P) :
    ‖X‖ = Real.sqrt (∫ ω, |X ω| ^ 2 ∂P) := by
  rw [norm_eq_sqrt_real_inner, l2_inner_formula]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change X ω * X ω = |X ω| ^ 2
    rw [sq_abs, pow_two]

variable [IsProbabilityMeasure P]

theorem covariance_formula (X Y : Ω → ℝ) (_hX : MemLp X 2 P) (_hY : MemLp Y 2 P) :
    covariance X Y P =
      ∫ ω, (X ω - ∫ a, X a ∂P) * (Y ω - ∫ a, Y a ∂P) ∂P := rfl

theorem extended_variance_finite_bridge (X : Ω → ℝ) (hX : MemLp X 2 P) :
    ENNReal.ofReal (variance X P) = extendedVariance P X := by
  rw [variance_formula P X hX]
  exact ofReal_integral_eq_lintegral_ofReal
    ((hX.sub (memLp_const _)).integrable_sq) (ae_of_all _ fun _ => sq_nonneg _)

theorem standard_deviation_formula (X : Ω → ℝ) (hX : MemLp X 2 P) :
    lpNorm (fun ω => X ω - ∫ a, X a ∂P) 2 P = Real.sqrt (variance X P) := by
  change lpNorm (X - fun _ => ∫ a, X a ∂P) 2 P = _
  rw [finite_lp_formula P _ (by norm_num) (by norm_num) (hX.sub (memLp_const _))]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, sq_abs]
  rw [Real.sqrt_eq_rpow, variance_formula P X hX]
  norm_num

theorem covariance_inner_formula (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    covariance X Y P =
      ⟪(hX.sub (memLp_const (∫ a, X a ∂P))).toLp (X - fun _ => ∫ a, X a ∂P),
        (hY.sub (memLp_const (∫ a, Y a ∂P))).toLp (Y - fun _ => ∫ a, Y a ∂P)⟫_ℝ := by
  rw [l2_inner_formula]
  apply integral_congr_ae
  filter_upwards [(hX.sub (memLp_const (∫ a, X a ∂P))).coeFn_toLp,
    (hY.sub (memLp_const (∫ a, Y a ∂P))).coeFn_toLp] with ω hx hy
  simp only [hx, hy, Pi.sub_apply]

theorem convex_combination (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (x y a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    φ (a*x+(1-a)*y) ≤ a*φ x+(1-a)*φ y := by
  exact hφ.2 (mem_univ x) (mem_univ y) ha0 (sub_nonneg.mpr ha1) (by ring)

theorem jensen (X : Ω → ℝ) (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (hX : Integrable X P)
    (hφX : Integrable (fun ω => φ (X ω)) P) :
    φ (∫ ω, X ω ∂P) ≤ ∫ ω, φ (X ω) ∂P := by
  exact hφ.map_integral_le (hφ.continuousOn isOpen_univ) isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) hX hφX

theorem lp_monotone (X : Ω → ℝ) (hX : AEStronglyMeasurable X P)
    {p q : ℝ≥0∞} (_hp : 0 < p) (hpq : p ≤ q) :
    eLpNorm X p P ≤ eLpNorm X q P :=
  eLpNorm_le_eLpNorm_of_exponent_le hpq hX

theorem minkowski (X Y : Ω → ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : MemLp X p P) (_hY : MemLp Y p P) :
    lpNorm (X+Y) p P ≤ lpNorm X p P + lpNorm Y p P := lpNorm_add_le hX hp

theorem cauchy_schwarz (X Y : Lp ℝ 2 P) :
    |∫ ω, X ω * Y ω ∂P| ≤ ‖X‖ * ‖Y‖ := by
  rw [← l2_inner_formula]
  exact abs_real_inner_le_norm X Y

theorem holder (X Y : Ω → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal q) P) :
    |∫ ω, X ω * Y ω ∂P| ≤ lpNorm X (ENNReal.ofReal p) P * lpNorm Y (ENNReal.ofReal q) P := by
  calc
    |∫ ω, X ω * Y ω ∂P| ≤ ∫ ω, ‖X ω * Y ω‖ ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P) (fun ω => X ω * Y ω)
    _ = ∫ ω, ‖X ω‖ * ‖Y ω‖ ∂P := by simp only [norm_mul]
    _ ≤ (∫ ω, ‖X ω‖ ^ p ∂P) ^ (1/p) * (∫ ω, ‖Y ω‖ ^ q ∂P) ^ (1/q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hX hY
    _ = _ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.pos)) (by finiteness) hX.1,
        lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.symm.pos)) (by finiteness) hY.1]
      simp only [ENNReal.toReal_ofReal hpq.nonneg, ENNReal.toReal_ofReal hpq.symm.nonneg,
        one_div]

theorem holder_endpoint (X Y : Ω → ℝ) (hX : MemLp X 1 P) (hY : MemLp Y ∞ P) :
    |∫ ω, X ω * Y ω ∂P| ≤ lpNorm X 1 P * lpNorm Y ∞ P := by
  have hXY : Integrable (fun ω => X ω * Y ω) P := by
    simpa only [Pi.mul_apply, mul_comm] using (hX.mul hY).integrable le_rfl
  calc
    |∫ ω, X ω * Y ω ∂P| ≤ ∫ ω, ‖X ω * Y ω‖ ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P) (fun ω => X ω * Y ω)
    _ ≤ ∫ ω, ‖X ω‖ * lpNorm Y ∞ P ∂P := by
      apply integral_mono_ae hXY.norm ((hX.integrable le_rfl).norm.mul_const _)
      filter_upwards [ae_le_lpNorm_exponent_top hY] with ω hy
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hy (norm_nonneg (X ω))
    _ = _ := by rw [integral_mul_const, lpNorm_one_eq_integral_norm hX.1]

theorem power_convex {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ r) := by
  exact convexOn_rpow hr

lemma signedExtendedIntegral_eq_integral {f : Ω → ℝ} (hf : Integrable f P) :
    signedExtendedIntegral P f = (∫ ω, f ω ∂P : ℝ) := by
  unfold signedExtendedIntegral
  have hneg : Integrable (fun ω => -f ω) P := hf.neg
  have h1 := EReal.coe_ennreal_toReal hf.lintegral_lt_top.ne
  have h2 := EReal.coe_ennreal_toReal hneg.lintegral_lt_top.ne
  rw [← h1, ← h2, ← EReal.coe_sub,
    ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

theorem signed_natural_moment_finite (X : Ω → ℝ) (n : ℕ)
    (h : Integrable (fun ω => X ω ^ n) P) :
    signedNaturalMoment P X n = some (moment X n P : EReal) := by
  rw [signedNaturalMoment, if_neg (fun hh => h.lintegral_lt_top.ne hh.1),
    signedExtendedIntegral_eq_integral P h]
  rfl

theorem signed_natural_moment_undefined (X : Ω → ℝ) (n : ℕ) :
    signedNaturalMoment P X n = none ↔
      (∫⁻ ω, ENNReal.ofReal (X ω ^ n) ∂P) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal (-(X ω ^ n)) ∂P) = ∞ := by
  simp only [signedNaturalMoment]
  split_ifs <;> simp_all

/-- Jensen also permits an infinite positive expectation; its negative part is finite. -/
theorem jensen_extended (X : Ω → ℝ) (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (hX : Integrable X P) :
    (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ∞ ∧
    (φ (∫ ω, X ω ∂P) : EReal) ≤ signedExtendedIntegral P (fun ω => φ (X ω)) := by
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hm : AEStronglyMeasurable (fun ω => φ (X ω)) P :=
    hc.comp_aestronglyMeasurable hX.1
  obtain ⟨l, c, hl, _⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ)
    (mem_univ (0 : ℝ)) (show φ 0 - 1 < φ 0 by linarith) isClosed_univ
    (hc.lowerSemicontinuous.lowerSemicontinuousOn univ) hφ
  have ha : Integrable (fun ω => l (X ω) + c) P :=
    (l.integrable_comp hX).add (integrable_const c)
  have hneg : (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ∞ := by
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (-(l (X ω) + c)) ∂P := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        have hb := hl ⟨X ω, mem_univ _⟩
        change l (X ω) + c ≤ φ (X ω) at hb
        linarith
      _ < ∞ := ha.neg.lintegral_lt_top
  refine ⟨hneg, ?_⟩
  by_cases hf : Integrable (fun ω => φ (X ω)) P
  · rw [signedExtendedIntegral_eq_integral P hf]
    exact_mod_cast jensen P X φ hφ hX hf
  · have hpos : (∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) = ∞ := by
      by_contra hp
      apply hf
      have hpint : Integrable (fun ω => max (φ (X ω)) 0) P := by
        refine ⟨(hm.aemeasurable.max aemeasurable_const).aestronglyMeasurable,
          (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => le_max_right (φ (X ω)) (0 : ℝ))).2 ?_⟩
        simpa [ENNReal.ofReal_max] using lt_top_iff_ne_top.mpr hp
      have hnint : Integrable (fun ω => max (-φ (X ω)) 0) P := by
        refine ⟨(hm.aemeasurable.neg.max aemeasurable_const).aestronglyMeasurable,
          (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => le_max_right (-φ (X ω)) (0 : ℝ))).2 ?_⟩
        simpa [ENNReal.ofReal_max] using hneg
      apply (hpint.sub hnint).congr
      exact ae_of_all _ fun ω => by
        dsimp only [Pi.sub_apply]
        simp only [max_def]
        split_ifs <;> linarith
    unfold signedExtendedIntegral
    rw [hpos, EReal.coe_ennreal_top, EReal.top_sub (by simpa using hneg.ne)]
    exact le_top

def fairCoin : Measure Bool := (PMF.bernoulli (1/2) (by norm_num)).toMeasure
def coinOne : Bool → ℝ := fun b => if b then 1 else 0
def coinZero : Bool → ℝ := fun b => if b then 0 else 1

lemma integral_fairCoin (f : Bool → ℝ) :
    (∫ b, f b ∂fairCoin) = (f false + f true) / 2 := by
  rw [fairCoin, PMF.integral_eq_sum]
  norm_num [PMF.bernoulli_apply]
  ring

lemma fairCoin_lp_values {p : ℝ} (hp : 0 < p) :
    lpNorm coinOne (ENNReal.ofReal p) fairCoin = (1/2 : ℝ) ^ p⁻¹ ∧
    lpNorm coinZero (ENNReal.ofReal p) fairCoin = (1/2 : ℝ) ^ p⁻¹ ∧
    lpNorm (coinOne + coinZero) (ENNReal.ofReal p) fairCoin = 1 := by
  have hm (f : Bool → ℝ) : AEStronglyMeasurable f fairCoin :=
    (measurable_of_countable f).aestronglyMeasurable
  have he (f : Bool → ℝ) := lpNorm_eq_integral_norm_rpow_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) (by finiteness) (hm f)
  simp only [ENNReal.toReal_ofReal hp.le] at he
  simp only [he, integral_fairCoin, coinOne, coinZero, Pi.add_apply,
    Bool.false_eq_true, ↓reduceIte, Real.norm_eq_abs, abs_zero, abs_one,
    Real.zero_rpow hp.ne', Real.one_rpow, zero_add, add_zero, one_add_one_eq_two,
    div_self (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

theorem small_exponent_counterexample {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    lpNorm (coinOne + coinZero) (ENNReal.ofReal p) fairCoin >
      lpNorm coinOne (ENNReal.ofReal p) fairCoin + lpNorm coinZero (ENNReal.ofReal p) fairCoin := by
  obtain ⟨h1, h0, hs⟩ := fairCoin_lp_values hp
  rw [h1, h0, hs]
  have hr : 1 < p⁻¹ := (one_lt_inv₀ hp).2 hp1
  have hh : (1/2 : ℝ)^p⁻¹ < 1/2 := by
    calc
      _ < (1/2 : ℝ)^1 := Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) hr
      _ = _ := Real.rpow_one _
  linarith

end HDP
