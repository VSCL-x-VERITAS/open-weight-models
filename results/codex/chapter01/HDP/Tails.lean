import Mathlib

/-! Tails, expectation and classical tail inequalities from Chapter 1, pp. 7–8. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace HDP.Tails

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

def cdf (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ := P.real {ω | X ω ≤ t}
def positiveExpectation (P : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (X ω) ∂P
def negativeExpectation (P : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (-X ω) ∂P
def signedExpectation (P : Measure Ω) (X : Ω → ℝ) : Option EReal :=
  if positiveExpectation P X = ∞ ∧ negativeExpectation P X = ∞ then none
  else some ((positiveExpectation P X : EReal) - (negativeExpectation P X : EReal))
def positiveTailIntegral (P : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, P {ω | t < X ω}
def negativeTailIntegral (P : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Iio 0, P {ω | X ω < t}
def weightedTailIntegral (P : Measure Ω) (X : Ω → ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (p * t ^ (p - 1)) * P {ω | t < |X ω|}
def eventIndicator (s : Set Ω) : Ω → ℝ := s.indicator (fun _ => 1)

variable {P : Measure Ω} {Q : Measure Ξ} {X : Ω → ℝ} {Y : Ξ → ℝ} {t p : ℝ}

theorem indicator_split (x t : ℝ) :
    x = x * eventIndicator {y : ℝ | t ≤ y} x + x * eventIndicator {y : ℝ | y < t} x := by
  classical
  by_cases h : t ≤ x <;> simp [eventIndicator, h, not_lt.mpr, lt_of_not_ge]

theorem constant_interval_integral (x : ℝ) : (∫ t : ℝ in 0..x, (1 : ℝ)) = x := by
  simp

theorem nonnegative_indicator_integral (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in Ioi 0, eventIndicator {s : ℝ | s < x} t) = x := by
  change (∫ t in Ioi 0, (Iio x).indicator (1 : ℝ → ℝ) t) = x
  rw [integral_indicator_one measurableSet_Iio,
    measureReal_restrict_apply measurableSet_Iio]
  have hs : Iio x ∩ Ioi (0 : ℝ) = Ioo 0 x := by ext t; simp [and_comm]
  rw [hs, Real.volume_real_Ioo_of_le hx, sub_zero]

theorem abs_sub_ge_iff_sq_ge (x μ : ℝ) (ht : 0 < t) :
    t ≤ |x - μ| ↔ t ^ 2 ≤ (x - μ) ^ 2 := by
  constructor
  · intro h
    nlinarith [sq_abs (x - μ)]
  · intro h
    nlinarith [sq_abs (x - μ), abs_nonneg (x - μ)]

private theorem positive_part_layercake (hX : AEMeasurable X P) :
    positiveExpectation P X = positiveTailIntegral P X := by
  have h := lintegral_eq_lintegral_meas_lt P
    (f := fun ω => max (X ω) 0) (Eventually.of_forall (fun ω => le_max_right _ _))
    (hX.max aemeasurable_const)
  simp only [positiveExpectation, positiveTailIntegral]
  calc
    (∫⁻ ω, ENNReal.ofReal (X ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (max (X ω) 0) ∂P := by
          congr 1
          funext ω
          simp
    _ = ∫⁻ t in Ioi 0, P {ω | t < max (X ω) 0} := h
    _ = ∫⁻ t in Ioi 0, P {ω | t < X ω} := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      apply congrArg P
      ext ω
      simp only [mem_setOf_eq, lt_max_iff]
      exact or_iff_left (not_lt.mpr ht.le)

private theorem reflected_negative_tail :
    positiveTailIntegral P (fun ω => -X ω) = negativeTailIntegral P X := by
  let f : ℝ → ℝ≥0∞ := fun t => P {ω | X ω < t}
  have hm : Measurable f := Monotone.measurable (fun a b hab =>
    measure_mono (fun ω hω => hω.trans_le hab))
  have h := setLIntegral_map (μ := (volume : Measure ℝ))
    (s := Iio 0) measurableSet_Iio hm (measurable_neg : Measurable (fun x : ℝ => -x))
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  have hs : (fun x : ℝ => -x) ⁻¹' Iio 0 = Ioi 0 := by ext x; simp
  rw [hs] at h
  rw [positiveTailIntegral, negativeTailIntegral, h]
  congr 1
  funext t
  change P {ω | t < -X ω} = P {ω | X ω < -t}
  apply congrArg P
  ext ω
  simp only [mem_setOf_eq]
  constructor <;> intro hω <;> linarith

private theorem positive_tail_real (hX : Integrable X P) :
    (∫ t in Ioi 0, P.real {ω | t < X ω}) = (positiveTailIntegral P X).toReal := by
  have hm : Measurable (fun t : ℝ => P {ω | t < X ω}) :=
    Antitone.measurable (fun a b hab => measure_mono (fun ω hω => hab.trans_lt hω))
  change (∫ t in Ioi 0, (P {ω | t < X ω}).toReal) = (positiveTailIntegral P X).toReal
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hm.ennreal_toReal.aestronglyMeasurable]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact ENNReal.ofReal_toReal (hX.measure_gt_lt_top ht).ne

private theorem reflected_negative_tail_real :
    (∫ t in Ioi 0, P.real {ω | t < -X ω}) =
      ∫ t in Iio 0, P.real {ω | X ω < t} := by
  calc
    _ = ∫ t in Ioi 0, P.real {ω | X ω < -t} := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply congrArg (fun s : Set Ω => P.real s)
      ext ω
      simp only [mem_setOf_eq]
      constructor <;> intro hω <;> linarith
    _ = ∫ t in Iic (- (0 : ℝ)), P.real {ω | X ω < t} :=
      integral_comp_neg_Ioi 0 (fun t => P.real {ω | X ω < t})
    _ = ∫ t in Iio 0, P.real {ω | X ω < t} := by
      rw [neg_zero, restrict_Iio_eq_restrict_Iic]

private theorem tail_probability_measurable :
    Measurable (fun t : ℝ => P {ω | t < |X ω|}) :=
  Antitone.measurable (fun a b hab => measure_mono (fun ω hω => hab.trans_lt hω))

private theorem weighted_integrand_measurable (p : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 1)) * P {ω | t < |X ω|}) :=
  ((measurable_const.mul (measurable_id.pow_const (p - 1))).ennreal_ofReal).mul
    tail_probability_measurable

theorem tail_eq_one_sub_cdf [IsProbabilityMeasure P] (hX : Measurable X) (t : ℝ) :
    P.real {ω | t < X ω} = 1 - cdf P X t := by
  have hs : {ω | t < X ω} = {ω | X ω ≤ t}ᶜ := by ext ω; simp
  rw [hs, probReal_compl_eq_one_sub (measurableSet_le hX measurable_const)]
  rfl

theorem distribution_determined_by_cdf [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : Measurable X) (hY : Measurable Y) (h : ∀ t, cdf P X t = cdf Q Y t) :
    Measure.map X P = Measure.map Y Q := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure (Q.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  apply Measure.eq_of_cdf
  ext t
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    map_measureReal_apply hX measurableSet_Iic, map_measureReal_apply hY measurableSet_Iic]
  exact h t

theorem nonnegative_integral_identity (hX : AEMeasurable X P) (h0 : 0 ≤ᵐ[P] X) :
    positiveExpectation P X = positiveTailIntegral P X :=
  lintegral_eq_lintegral_meas_lt P h0 hX

theorem nonnegative_integral_finite_iff (hX : AEMeasurable X P) (h0 : 0 ≤ᵐ[P] X) :
    positiveExpectation P X < ∞ ↔ positiveTailIntegral P X < ∞ := by
  rw [nonnegative_integral_identity hX h0]

theorem nonnegative_integral_infinite_iff (hX : AEMeasurable X P) (h0 : 0 ≤ᵐ[P] X) :
    positiveExpectation P X = ∞ ↔ positiveTailIntegral P X = ∞ := by
  rw [nonnegative_integral_identity hX h0]

theorem signed_parts_via_tails (hX : AEMeasurable X P) :
    positiveExpectation P X = positiveTailIntegral P X ∧
      negativeExpectation P X = negativeTailIntegral P X := by
  refine ⟨positive_part_layercake hX, ?_⟩
  exact (positive_part_layercake hX.neg).trans reflected_negative_tail

theorem signed_integral_identity (hX : AEMeasurable X P) :
    signedExpectation P X =
      if positiveTailIntegral P X = ∞ ∧ negativeTailIntegral P X = ∞ then none
      else some ((positiveTailIntegral P X : EReal) - (negativeTailIntegral P X : EReal)) := by
  rw [signedExpectation, (signed_parts_via_tails hX).1, (signed_parts_via_tails hX).2]

theorem signed_integral_undefined_iff (hX : AEMeasurable X P) :
    signedExpectation P X = none ↔
      positiveTailIntegral P X = ∞ ∧ negativeTailIntegral P X = ∞ := by
  rw [signed_integral_identity hX]
  split_ifs <;> simp_all

theorem signed_integral_identity_integrable (hX : Integrable X P) :
    (∫ ω, X ω ∂P) = (∫ t in Ioi 0, P.real {ω | t < X ω}) -
      (∫ t in Iio 0, P.real {ω | X ω < t}) := by
  rw [← reflected_negative_tail_real, positive_tail_real hX]
  have hneg := positive_tail_real hX.neg
  change (∫ t in Ioi 0, P.real {ω | t < -X ω}) =
    (positiveTailIntegral P (fun ω => -X ω)).toReal at hneg
  rw [hneg]
  rw [← (signed_parts_via_tails hX.aemeasurable).1,
    ← positive_part_layercake (X := fun ω => -X ω) hX.neg.aemeasurable]
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hX

theorem absolute_moment_via_tails (hX : AEMeasurable X P) (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂P) = weightedTailIntegral P X p := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul P
    (Eventually.of_forall (fun ω => abs_nonneg (X ω))) hX.abs hp]
  rw [weightedTailIntegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext t
  rw [ENNReal.ofReal_mul hp.le]
  ac_rfl

theorem absolute_moment_integrable_of_tail_finite (hX : AEMeasurable X P) (hp : 0 < p)
    (hfinite : weightedTailIntegral P X p < ∞) : Integrable (fun ω => |X ω| ^ p) P := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hX.abs.pow_const p).aestronglyMeasurable
    (Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg _) _))).1
  rw [absolute_moment_via_tails hX hp]
  exact hfinite.ne

theorem absolute_moment_via_tails_finite (hX : AEMeasurable X P) (hp : 0 < p)
    (hfinite : weightedTailIntegral P X p < ∞) :
    (∫ ω, |X ω| ^ p ∂P) = (weightedTailIntegral P X p).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg _) _))
    (hX.abs.pow_const p).aestronglyMeasurable, absolute_moment_via_tails hX hp]

/-- The weighted ENNReal integral is the source's literal real integral on probability spaces. -/
theorem weighted_tail_toReal [IsProbabilityMeasure P] (hp : 0 < p) :
    (weightedTailIntegral P X p).toReal =
      ∫ t in Ioi 0, p * t ^ (p - 1) * P.real {ω | t < |X ω|} := by
  rw [weightedTailIntegral, ← integral_toReal (weighted_integrand_measurable p).aemeasurable]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg hp.le (Real.rpow_nonneg ht.le _))]
    rfl
  · filter_upwards [] with t
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top P _)

theorem absolute_moment_via_real_tails [IsProbabilityMeasure P]
    (hX : AEMeasurable X P) (hp : 0 < p) (hfinite : weightedTailIntegral P X p < ∞) :
    (∫ ω, |X ω| ^ p ∂P) =
      ∫ t in Ioi 0, p * t ^ (p - 1) * P.real {ω | t < |X ω|} := by
  rw [absolute_moment_via_tails_finite hX hp hfinite, weighted_tail_toReal hp]

theorem weighted_real_tail_integrable [IsProbabilityMeasure P] (hp : 0 < p)
    (hfinite : weightedTailIntegral P X p < ∞) :
    IntegrableOn (fun t : ℝ => p * t ^ (p - 1) * P.real {ω | t < |X ω|}) (Ioi 0) := by
  have hi := integrable_toReal_of_lintegral_ne_top
    (weighted_integrand_measurable (P := P) (X := X) p).aemeasurable hfinite.ne
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (mul_nonneg hp.le (Real.rpow_nonneg ht.le _))]
  rfl

theorem markov (hX : AEMeasurable X P) (h0 : 0 ≤ᵐ[P] X) (ht : 0 < t) :
    P {ω | t ≤ X ω} ≤ positiveExpectation P X / ENNReal.ofReal t := by
  have h := meas_ge_le_lintegral_div hX.ennreal_ofReal
    (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top
  convert h using 1
  apply congrArg P
  ext ω
  simp only [mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff']
  exact (or_iff_left ht.not_ge).symm

theorem markov_integrable (hX : Integrable X P) (h0 : 0 ≤ᵐ[P] X) (ht : 0 < t) :
    P.real {ω | t ≤ X ω} ≤ (∫ ω, X ω ∂P) / t := by
  apply (le_div_iff₀ ht).2
  simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg h0 hX t

theorem chebyshev [IsProbabilityMeasure P] (hX : MemLp X 2 P) (ht : 0 < t) :
    P.real {ω | t ≤ |X ω - ∫ a, X a ∂P|} ≤ ProbabilityTheory.variance X P / t ^ 2 := by
  have hc : MemLp (fun ω => X ω - ∫ a, X a ∂P) 2 P :=
    hX.sub (memLp_const _)
  have hs := markov_integrable hc.integrable_sq
    (Eventually.of_forall (fun ω => sq_nonneg (X ω - ∫ a, X a ∂P))) (sq_pos_of_pos ht)
  rw [← ProbabilityTheory.variance_eq_integral hX.aemeasurable] at hs
  convert hs using 1
  apply congrArg (fun s : Set Ω => P.real s)
  ext ω
  exact abs_sub_ge_iff_sq_ge (X ω) (∫ a, X a ∂P) ht

end HDP.Tails
