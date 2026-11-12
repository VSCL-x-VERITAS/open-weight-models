/-
Section 1.2, second part: the integral identity (Lemma 1.2.1), its two exercises,
Markov's inequality, Chebyshev's inequality, and the CDF/tail relation.
-/
import Mathlib
import HDP.Basic
import HDP.Inequalities

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Lemma 1.2.1 (integral identity), real form for an integrable non-negative variable. -/
theorem integral_eq_integral_tail [IsProbabilityMeasure μ] (hX : Integrable X μ)
    (hX_nonneg : 0 ≤ᵐ[μ] X) :
    ∫ ω, X ω ∂μ = ∫ t in Set.Ioi 0, tail μ X t :=
  hX.integral_eq_integral_meas_lt hX_nonneg

/-- Lemma 1.2.1 in `ℝ≥0∞` form: it holds for every a.e.-non-negative measurable
variable, and the two sides are finite or infinite simultaneously. -/
theorem lintegral_eq_lintegral_tail (hX : AEMeasurable X μ) (hX_nonneg : 0 ≤ᵐ[μ] X) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ∫⁻ t in Set.Ioi 0, μ {ω | t < X ω} :=
  lintegral_eq_lintegral_meas_lt μ hX_nonneg hX

/-- Exercise 1.2.2: the signed extension of the integral identity.  The second
integral is written over `(-∞, 0]`; the source writes it over `(-∞, 0)`, and the
two differ only at the endpoint `0`, which is a null set for Lebesgue measure. -/
theorem integral_eq_tail_sub_lower [IsProbabilityMeasure μ] (hX : Integrable X μ) :
    ∫ ω, X ω ∂μ =
      (∫ t in Set.Ioi 0, tail μ X t) - ∫ t in Set.Iic 0, μ.real {ω | X ω < t} := by
  let Xp : Ω → ℝ := fun ω => max (X ω) 0
  let Xm : Ω → ℝ := fun ω => max (-(X ω)) 0
  have hXp_int : Integrable Xp μ := hX.pos_part
  have hXm_int : Integrable Xm μ := hX.neg_part
  have hXp_nonneg : 0 ≤ᵐ[μ] Xp := ae_of_all _ fun ω => le_max_right _ _
  have hXm_nonneg : 0 ≤ᵐ[μ] Xm := ae_of_all _ fun ω => le_max_right _ _
  have hXp_eq : ∫ ω, Xp ω ∂μ = ∫ t in Set.Ioi 0, tail μ X t := by
    rw [Integrable.integral_eq_integral_meas_lt hXp_int hXp_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    change μ.real {ω | t < Xp ω} = μ.real {ω | t < X ω}
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Xp]
    constructor
    · intro h
      rcases lt_max_iff.mp h with h' | h'
      · exact h'
      · exfalso; exact (not_lt_of_ge ht.le) h'
    · intro h
      exact lt_of_lt_of_le h (le_max_left _ _)
  have hXm_eq : ∫ ω, Xm ω ∂μ = ∫ t in Set.Iic 0, μ.real {ω | X ω < t} := by
    calc
      ∫ ω, Xm ω ∂μ = ∫ t in Set.Ioi 0, μ.real {ω | t < Xm ω} :=
        Integrable.integral_eq_integral_meas_lt hXm_int hXm_nonneg
      _ = ∫ t in Set.Ioi 0, μ.real {ω | X ω < -t} := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t ht
        change μ.real {ω | t < Xm ω} = μ.real {ω | X ω < -t}
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, Xm]
        constructor
        · intro h
          rcases lt_max_iff.mp h with h' | h'
          · linarith
          · exfalso; exact (not_lt_of_ge ht.le) h'
        · intro h
          exact lt_of_lt_of_le (by linarith : t < -(X ω)) (le_max_left _ _)
      _ = ∫ t in Set.Iic 0, μ.real {ω | X ω < t} := by
        rw [integral_comp_neg_Ioi (c := 0) (f := fun t => μ.real {ω | X ω < t})]
        simp
  have hsplit : X = fun ω => Xp ω - Xm ω := by
    ext ω
    by_cases hω : 0 ≤ X ω
    · simp [Xp, Xm, max_eq_left hω, max_eq_right (neg_nonpos.mpr hω)]
    · push_neg at hω
      simp [Xp, Xm, max_eq_right hω.le, max_eq_left (neg_nonneg.mpr hω.le)]
  calc
    ∫ ω, X ω ∂μ = ∫ ω, (Xp ω - Xm ω) ∂μ := by rw [hsplit]
    _ = ∫ ω, Xp ω ∂μ - ∫ ω, Xm ω ∂μ := integral_sub hXp_int hXm_int
    _ = (∫ t in Set.Ioi 0, tail μ X t) - ∫ t in Set.Iic 0, μ.real {ω | X ω < t} := by
      rw [hXp_eq]
      exact congrArg (fun z => (∫ t in Set.Ioi 0, tail μ X t) - z) hXm_eq

/-- Exercise 1.2.3, in `ℝ≥0∞` form: `E |X|^p = ∫_0^∞ p t^{p-1} P(|X| > t) dt`
without any finiteness assumption. -/
theorem absMoment_eq_integral_tail_ennreal {p : ℝ} (hp : 0 < p) (hX : AEMeasurable X μ) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ =
      ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi 0, μ {ω | t < |X ω|} * ENNReal.ofReal (t ^ (p - 1)) := by
  simpa using
    (lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ) (f := fun ω => |X ω|)
      (ae_of_all _ fun _ => abs_nonneg _) hX.abs hp)

/-- Markov's inequality (Proposition 1.2.4). -/
theorem markov [IsProbabilityMeasure μ] (hX_nonneg : 0 ≤ᵐ[μ] X) (hX : Integrable X μ)
    {t : ℝ} (ht : 0 < t) : μ.real {ω | t ≤ X ω} ≤ (∫ ω, X ω ∂μ) / t := by
  rw [le_div_iff₀ ht]
  simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg hX_nonneg hX t

/-- Chebyshev's inequality (Corollary 1.2.5). -/
theorem chebyshev [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - μ[X]|} ≤ variance X μ / t ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := μ) hX ht
  have h' : μ.real {ω | t ≤ |X ω - μ[X]|} ≤ (ENNReal.ofReal (variance X μ / t ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg t))] at h'

/-- Exercise 1.2.6: Chebyshev's inequality deduced from Markov's inequality applied to
`(X - E X)^2` at threshold `t^2`. -/
theorem chebyshev_from_markov [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - μ[X]|} ≤ variance X μ / t ^ 2 := by
  let Y : Ω → ℝ := fun ω => (X ω - μ[X]) ^ 2
  have hY_nonneg : 0 ≤ᵐ[μ] Y := ae_of_all _ fun _ => sq_nonneg _
  have hY_int : Integrable Y μ := (hX.sub (memLp_const (μ[X]))).integrable_sq
  have hmark := markov (μ := μ) (X := Y) hY_nonneg hY_int (t := t ^ 2) (by positivity)
  have hset : {ω | t ≤ |X ω - μ[X]|} = {ω | t ^ 2 ≤ Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Y]
    constructor
    · intro h
      nlinarith [abs_nonneg (X ω - μ[X]), sq_abs (X ω - μ[X])]
    · intro h
      by_contra hlt
      push_neg at hlt
      nlinarith [abs_nonneg (X ω - μ[X]), sq_abs (X ω - μ[X])]
  rw [hset]
  have hvar : variance X μ = ∫ ω, Y ω ∂μ := by
    rw [variance_eq_integral hX.aemeasurable]
  rw [hvar]
  simpa [hvar, div_eq_mul_inv, mul_comm] using hmark

/-- The CDF as a measure of the half-line. -/
theorem cdfOf_eq_measureReal [IsProbabilityMeasure μ] (hX : AEMeasurable X μ) (t : ℝ) :
    cdfOf μ X t = μ.real {ω | X ω ≤ t} := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  rw [cdfOf, cdf_eq_real]
  change ((μ.map X) (Set.Iic t)).toReal = (μ (X ⁻¹' Set.Iic t)).toReal
  rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iic]

/-- Tails are one minus the CDF. -/
theorem tail_eq_one_sub_cdf [IsProbabilityMeasure μ] (hX : AEMeasurable X μ) (t : ℝ) :
    tail μ X t = 1 - cdfOf μ X t := by
  rw [cdfOf_eq_measureReal hX]
  have hnull : NullMeasurableSet {ω | X ω ≤ t} μ :=
    nullMeasurableSet_le hX aemeasurable_const
  have hcompl : μ.real {ω | t < X ω} = μ.real {ω | X ω ≤ t}ᶜ := by
    congr 1
    ext ω
    simp [not_le]
  rw [tail, hcompl, measureReal_compl₀ hnull]
  simp [probReal_univ]

/-- Markov's inequality in `ℝ≥0∞` form, requiring only a.e. measurability and
a.e. non-negativity (no integrability). -/
theorem markov_ennreal [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
    (hX_nonneg : 0 ≤ᵐ[μ] X) {t : ℝ} (ht : 0 < t) :
    μ {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (X ω)} * ENNReal.ofReal t ≤
      ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (X ω)) μ := hX.ennreal_ofReal
  have := mul_meas_ge_le_lintegral₀ (μ := μ) (f := fun ω => ENNReal.ofReal (X ω)) hmeas
    (ENNReal.ofReal t)
  simpa [mul_comm] using this

end HDP
