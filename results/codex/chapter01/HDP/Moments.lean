import HDP.Basic

/-! # Raw moments under operator clarification 001

`assisted_continuation_001` formalizes the supplied Chapter 1 with the explicit
domain correction in `source/operator-clarification-001/CLARIFICATION.txt`.
Signed real raw moments have positive natural orders and ordinary integer powers.
Nonnegative raw moments and arbitrary signed absolute moments have real orders
`p > 0`. Their nonnegative extended expectations retain infinity; signed extended
expectations retain either one-sided infinity and leave infinity-minus-infinity
undefined. Real-valued bridges require genuine integrability or extended finiteness.

The retained definitions in `HDP.Basic` are reused without alteration. Their
total auxiliary values at zero or other orders make no source-domain assertion.
No general signed noninteger raw moment, complex moment, negative-base `rpow`
extension, or special rational-power convention is adopted. This is an explicit
operator-assisted amendment, not a theorem about the PDF's unrestricted wording.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HDP
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem nonnegative_raw_moment_finite_iff (X : Ω → ℝ≥0)
    (hX : AEMeasurable (fun ω => (X ω : ℝ)) P) {p : ℝ} (_hp : 0 < p) :
    nonnegativeRawMoment P X p < ∞ ↔
      Integrable (fun ω => (X ω : ℝ) ^ p) P := by
  have hm : AEStronglyMeasurable (fun ω => (X ω : ℝ) ^ p) P :=
    (hX.pow_const p).aestronglyMeasurable
  have hn : 0 ≤ᵐ[P] (fun ω => (X ω : ℝ) ^ p) :=
    ae_of_all _ fun ω => Real.rpow_nonneg (X ω).coe_nonneg _
  exact ⟨fun h => ⟨hm, (hasFiniteIntegral_iff_ofReal hn).2 h⟩,
    fun h => (hasFiniteIntegral_iff_ofReal hn).1 h.2⟩

theorem nonnegative_raw_moment_finite_bridge (X : Ω → ℝ≥0) {p : ℝ}
    (_hp : 0 < p) (h : Integrable (fun ω => (X ω : ℝ) ^ p) P) :
    ENNReal.ofReal (∫ ω, (X ω : ℝ) ^ p ∂P) = nonnegativeRawMoment P X p := by
  exact ofReal_integral_eq_lintegral_ofReal h
    (ae_of_all _ fun ω => Real.rpow_nonneg (X ω).coe_nonneg _)

theorem nonnegative_raw_moment_toReal (X : Ω → ℝ≥0)
    (hX : AEMeasurable (fun ω => (X ω : ℝ)) P) {p : ℝ} (hp : 0 < p)
    (hfinite : nonnegativeRawMoment P X p < ∞) :
    (nonnegativeRawMoment P X p).toReal = ∫ ω, (X ω : ℝ) ^ p ∂P := by
  have hi := (nonnegative_raw_moment_finite_iff P X hX hp).1 hfinite
  rw [← nonnegative_raw_moment_finite_bridge P X hp hi,
    ENNReal.toReal_ofReal (integral_nonneg fun ω => Real.rpow_nonneg (X ω).coe_nonneg _)]

theorem absolute_moment_finite_iff (X : Ω → ℝ) (hX : AEMeasurable X P)
    {p : ℝ} (_hp : 0 < p) :
    absoluteMoment P X p < ∞ ↔ Integrable (fun ω => |X ω| ^ p) P := by
  have hm : AEStronglyMeasurable (fun ω => |X ω| ^ p) P :=
    (hX.abs.pow_const p).aestronglyMeasurable
  have hn : 0 ≤ᵐ[P] (fun ω => |X ω| ^ p) :=
    ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) _
  exact ⟨fun h => ⟨hm, (hasFiniteIntegral_iff_ofReal hn).2 h⟩,
    fun h => (hasFiniteIntegral_iff_ofReal hn).1 h.2⟩

theorem absolute_moment_finite_bridge (X : Ω → ℝ) {p : ℝ} (_hp : 0 < p)
    (h : Integrable (fun ω => |X ω| ^ p) P) :
    ENNReal.ofReal (∫ ω, |X ω| ^ p ∂P) = absoluteMoment P X p := by
  exact ofReal_integral_eq_lintegral_ofReal h
    (ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) _)

theorem absolute_moment_toReal (X : Ω → ℝ) (hX : AEMeasurable X P)
    {p : ℝ} (hp : 0 < p) (hfinite : absoluteMoment P X p < ∞) :
    (absoluteMoment P X p).toReal = ∫ ω, |X ω| ^ p ∂P := by
  have hi := (absolute_moment_finite_iff P X hX hp).1 hfinite
  rw [← absolute_moment_finite_bridge P X hp hi,
    ENNReal.toReal_ofReal (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _)]

/-- Common-domain agreement includes infinite nonnegative expectations. -/
theorem nonnegative_integer_moment_agreement (X : Ω → ℝ≥0) (n : ℕ)
    (_hn : 0 < n) :
    signedNaturalMoment P (fun ω => (X ω : ℝ)) n =
      some (nonnegativeRawMoment P X (n : ℝ) : EReal) := by
  have hneg : (∫⁻ ω, ENNReal.ofReal (-((X ω : ℝ) ^ n)) ∂P) = 0 := by
    calc
      _ = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P := lintegral_congr fun ω =>
        ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (pow_nonneg (X ω).coe_nonneg n))
      _ = 0 := lintegral_zero
  simp only [signedNaturalMoment, signedExtendedIntegral, hneg, ENNReal.zero_ne_top,
    and_false, ↓reduceIte, EReal.coe_ennreal_zero, sub_zero,
    nonnegativeRawMoment, Real.rpow_natCast]

theorem nonnegative_integer_moment_finite_iff (X : Ω → ℝ≥0)
    (hX : AEMeasurable (fun ω => (X ω : ℝ)) P) (n : ℕ) (hn : 0 < n) :
    nonnegativeRawMoment P X (n : ℝ) < ∞ ↔
      Integrable (fun ω => (X ω : ℝ) ^ n) P := by
  simpa only [Real.rpow_natCast] using
    nonnegative_raw_moment_finite_iff P X hX (show 0 < (n : ℝ) from Nat.cast_pos.mpr hn)

theorem nonnegative_integer_moment_finite_bridge (X : Ω → ℝ≥0)
    (n : ℕ) (hn : 0 < n) (h : Integrable (fun ω => (X ω : ℝ) ^ n) P) :
    signedNaturalMoment P (fun ω => (X ω : ℝ)) n =
        some (moment (fun ω => (X ω : ℝ)) n P : EReal) ∧
      ENNReal.ofReal (moment (fun ω => (X ω : ℝ)) n P) =
        nonnegativeRawMoment P X (n : ℝ) := by
  refine ⟨signed_natural_moment_finite P (fun ω => (X ω : ℝ)) n h, ?_⟩
  rw [natural_moment_formula P (fun ω => (X ω : ℝ)) n h]
  simpa only [Real.rpow_natCast] using
    nonnegative_raw_moment_finite_bridge P X (show 0 < (n : ℝ) from Nat.cast_pos.mpr hn)
      (by simpa only [Real.rpow_natCast] using h)

end HDP
