/-
Foundations for the Poisson limit theorem: the Poisson law on `ℝ` and the
characteristic functions of the Poisson and Bernoulli laws.
-/
import Mathlib
import HDP.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal BigOperators Topology

namespace HDP


noncomputable def poissonReal (r : ℝ≥0) : Measure ℝ :=
  (poissonDist r).map (fun n : ℕ => (n : ℝ))

instance poissonDist_isProbability (r : ℝ≥0) : IsProbabilityMeasure (poissonDist r) := by
  unfold poissonDist
  infer_instance

instance poissonReal_isProbability (r : ℝ≥0) : IsProbabilityMeasure (poissonReal r) := by
  unfold poissonReal
  exact Measure.isProbabilityMeasure_map (measurable_of_countable (fun n : ℕ => (n : ℝ))).aemeasurable

lemma charFun_poissonReal (r : ℝ≥0) (t : ℝ) :
    charFun (poissonReal r) t = cexp ((r : ℂ) * (cexp ((t : ℂ) * I) - 1)) := by
  have hmeas : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _
  rw [charFun_apply_real]
  rw [poissonReal, integral_map hmeas.aemeasurable (by fun_prop : AEStronglyMeasurable (fun x:ℝ => cexp (t*x*I)) (poissonReal r))]
  rw [show poissonDist r = (poissonPMF r).toMeasure from rfl]
  have hfint : Integrable (fun n : ℕ => cexp ((t:ℂ) * ((n:ℝ):ℂ) * I)) (poissonDist r) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun n => ?_)
    rw [Complex.norm_exp]
    simp
  have hfint' : Integrable (fun n : ℕ => cexp ((t:ℂ) * ((n:ℝ):ℂ) * I)) ((poissonPMF r).toMeasure) := by
    simpa [poissonDist, poissonMeasure, mul_comm, mul_left_comm, mul_assoc] using hfint
  rw [PMF.integral_eq_tsum (poissonPMF r) (fun n : ℕ => cexp ((t:ℂ) * ((n:ℝ):ℂ) * I)) hfint']
  · have hterm : ∀ n : ℕ, (poissonPMF r n).toReal • cexp ((t:ℂ) * ((n:ℝ):ℂ) * I) =
        poissonPMFReal r n • cexp ((t:ℂ) * ((n:ℝ):ℂ) * I) := by
      intro n
      change (ENNReal.ofReal (poissonPMFReal r n)).toReal • cexp ((t:ℂ) * ((n:ℝ):ℂ) * I) = _
      rw [ENNReal.toReal_ofReal (poissonPMFReal_nonneg)]
    trans ∑' n : ℕ, poissonPMFReal r n • cexp ((t:ℂ) * ((n:ℝ):ℂ) * I)
    · exact tsum_congr hterm
    simp_rw [Complex.real_smul]
    have hfac : ∀ n : ℕ, (poissonPMFReal r n : ℂ) * cexp ((t:ℂ) * ((n:ℝ):ℂ) * I) =
        cexp (-(r:ℂ)) * ((r:ℂ) * cexp ((t:ℂ) * I))^n / (Nat.factorial n : ℂ) := by
      intro n
      rw [poissonPMFReal]
      push_cast
      rw [show cexp (↑t * ↑↑n * I) = cexp ((n:ℂ) * ((t:ℂ) * I)) by congr 1; ring,
        Complex.exp_nat_mul]
      calc
        cexp (-↑↑r) * ↑↑r ^ n * (↑n.factorial)⁻¹ * cexp (↑t * I) ^ n
            = cexp (-↑↑r) * (↑↑r * cexp (↑t * I))^n * (↑n.factorial)⁻¹ := by
              rw [mul_pow]; ring
        _ = cexp (-↑↑r) * (↑↑r * cexp (↑t * I))^n / (Nat.factorial n : ℂ) := by
              rw [div_eq_mul_inv]
    simp_rw [hfac]
    simp_rw [div_eq_mul_inv, mul_assoc]
    rw [tsum_mul_left]
    simp_rw [← div_eq_mul_inv]
    have hexp : cexp ((r:ℂ) * cexp ((t:ℂ) * I)) =
        ∑' n : ℕ, ((r:ℂ) * cexp ((t:ℂ) * I))^n / (Nat.factorial n : ℂ) := by
      have h := congrFun NormedSpace.exp_eq_tsum_div ((r:ℂ) * cexp ((t:ℂ) * I))
      rw [Complex.exp_eq_exp_ℂ] at h ⊢
      exact h
    rw [← hexp]
    rw [← Complex.exp_add]
    congr 1
    ring




lemma charFun_bernoulli (p : ℝ≥0) (hp : p ≤ 1) (t : ℝ) :
    charFun (bernoulliMeasure p) t = (1 - (p:ℂ)) + (p:ℂ) * cexp ((t:ℂ) * I) := by
  haveI : IsProbabilityMeasure (bernoulliMeasure p) := bernoulliMeasure_isProbability p hp
  rw [charFun_apply_real]
  rw [bernoulliMeasure, integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp only [ENNReal.coe_toReal]
    change ((p:ℝ):ℂ) * cexp ((t:ℝ) * 1 * I) + (((1 - p : ℝ≥0):ℝ):ℂ) * cexp ((t:ℝ) * 0 * I) =
      1 - ((p:ℝ):ℂ) + ((p:ℝ):ℂ) * cexp ((t:ℝ) * I)
    rw [NNReal.coe_sub hp]
    push_cast
    simp only [mul_one, mul_zero, zero_mul]
    rw [show cexp 0 = 1 from Complex.exp_zero]
    ring
  · exact (integrable_dirac (a := 1) (f := fun x : ℝ => cexp (t*x*I)) (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (a := 0) (f := fun x : ℝ => cexp (t*x*I)) (by simp)).smul_measure (by simp)


end HDP
