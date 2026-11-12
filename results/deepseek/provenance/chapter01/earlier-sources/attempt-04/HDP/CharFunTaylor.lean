/-
Second-order expansion of the characteristic function at zero, for a real random
variable with finite second moment, together with the pointwise Taylor estimates
used in the CLT proof.
-/
import Mathlib
import HDP.Basic
import HDP.LimitTheorems

open Filter Topology Complex MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators

namespace HDP

lemma norm_exp_sub_quadratic_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖cexp z - (1 + z + z^2 / 2)‖ ≤ (2/9 : ℝ) * ‖z‖^3 := by
  have h := Complex.exp_bound hz (n := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  simp only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one, div_one,
    zero_add] at h
  norm_num at h ⊢
  simpa [mul_comm] using h

lemma exp_quadratic_error_tendsto (x : ℝ) :
    Tendsto (fun s : ℝ => (cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I
      - ((s * x : ℂ) * I) ^ 2 / 2) / (s : ℂ) ^ 2) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_abs : Tendsto (fun s : ℝ => |s|) (𝓝[≠] (0:ℝ)) (𝓝 0) :=
    by simpa using (continuous_abs.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ), |s| ≤ 1 ∧ |s * x| ≤ 1 := by
    have h1 : ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ), |s| ≤ 1 :=
      h_abs.eventually (Iic_mem_nhds zero_lt_one)
    have h2 : ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ), |s * x| ≤ 1 := by
      have h2' : Tendsto (fun s : ℝ => |s| * |x|) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
        simpa using h_abs.mul_const |x|
      simpa [abs_mul] using h2'.eventually (Iic_mem_nhds zero_lt_one)
    exact h1.and h2
  have hb : ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ),
      ‖(cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I
        - ((s * x : ℂ) * I) ^ 2 / 2) / (s : ℂ) ^ 2‖ ≤ (2/9) * |x|^3 * |s| := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hsne
    have hz : ‖((s * x : ℂ) * I)‖ ≤ 1 := by
      simpa [norm_mul, Real.norm_eq_abs, abs_mul] using hs.2
    have h := norm_exp_sub_quadratic_le hz
    have hsabs : (0:ℝ) < |s| := abs_pos.mpr hsne
    calc
      ‖(cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I
          - ((s * x : ℂ) * I) ^ 2 / 2) / (s : ℂ) ^ 2‖
          = ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I
              - ((s * x : ℂ) * I) ^ 2 / 2‖ / ‖(s : ℂ) ^ 2‖ := by rw [norm_div]
      _ = ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I
              - ((s * x : ℂ) * I) ^ 2 / 2‖ / ‖(s : ℂ)‖ ^ 2 := by rw [norm_pow]
      _ = ‖cexp ((s * x : ℂ) * I) - (1 + (s * x : ℂ) * I + ((s * x : ℂ) * I) ^ 2 / 2)‖ /
            ‖(s : ℂ)‖ ^ 2 := by ring_nf
      _ ≤ ((2/9) * ‖((s * x : ℂ) * I)‖ ^ 3) / ‖(s : ℂ)‖ ^ 2 := by gcongr
      _ = (2/9) * |x|^3 * |s| := by
        rw [show ‖((s * x : ℂ) * I)‖ = |s * x| by
              simp [norm_mul, Complex.norm_I, Real.norm_eq_abs],
            show ‖(s : ℂ)‖ = |s| by simp [Real.norm_eq_abs],
            abs_mul]
        field_simp [hsabs.ne']
  have hlim : Tendsto (fun s : ℝ => (2/9) * |x|^3 * |s|) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have := h_abs.const_mul ((2/9) * |x|^3)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hlim



lemma exp_linear_error_tendsto (x : ℝ) :
    Tendsto (fun s : ℝ => (cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I) / (s : ℂ) ^ 2)
      (𝓝[≠] (0:ℝ)) (𝓝 (-(x:ℂ)^2 / 2)) := by
  have h : Tendsto (fun s : ℝ => (-(x:ℂ)^2 / 2) +
      (cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I - ((s * x : ℂ) * I) ^ 2 / 2) /
        (s : ℂ) ^ 2) (𝓝[≠] (0:ℝ)) (𝓝 (-(x:ℂ)^2 / 2)) := by
    simpa using tendsto_const_nhds.add (exp_quadratic_error_tendsto x)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp [hs0]
  rw [Complex.I_sq]
  ring



lemma norm_exp_linear_error_div_sq_le (x : ℝ) {s : ℝ} (hs : s ≠ 0) :
    ‖(cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I) / (s : ℂ) ^ 2‖ ≤ 3 * x^2 := by
  have hsabs : (0:ℝ) < |s| := abs_pos.mpr hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hnorm : ‖(cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I) / (s : ℂ) ^ 2‖ =
      ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖ / |s|^2 := by
    rw [norm_div, norm_pow]
    congr 1
    simp [Real.norm_eq_abs]
  rw [hnorm]
  by_cases hz : |s * x| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := (s * x : ℂ) * I) (by
      simpa [norm_mul, Real.norm_eq_abs, abs_mul] using hz)
    have hnormz : ‖((s * x : ℂ) * I)‖ = |s * x| := by
      simp [norm_mul, Complex.norm_I, Real.norm_eq_abs]
    have : ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖ ≤ |s * x|^2 := by
      simpa [hnormz] using h
    calc
      ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖ / |s|^2 ≤ |s * x|^2 / |s|^2 := by
        gcongr
      _ = x^2 := by
        rw [abs_mul, mul_pow]
        field_simp [hsabs.ne']
        rw [sq_abs]
      _ ≤ 3 * x^2 := by nlinarith [sq_nonneg x]
  · push_neg at hz
    have hzpos : 0 < |s * x| := lt_trans zero_lt_one hz
    have htri : ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖ ≤ 3 * |s * x| := by
      have hexp : ‖cexp ((s * x : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      calc
        ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖
            ≤ ‖cexp ((s * x : ℂ) * I)‖ + ‖(1 : ℂ)‖ + ‖((s * x : ℂ) * I)‖ := by
          calc
            ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖
                ≤ ‖cexp ((s * x : ℂ) * I) - 1‖ + ‖((s * x : ℂ) * I)‖ := norm_sub_le _ _
            _ ≤ (‖cexp ((s * x : ℂ) * I)‖ + ‖(1 : ℂ)‖) + ‖((s * x : ℂ) * I)‖ := by
              gcongr; exact norm_sub_le _ _
            _ = _ := by ring
        _ = 1 + 1 + |s * x| := by simp [hexp, norm_mul, Complex.norm_I, Real.norm_eq_abs]
        _ ≤ 3 * |s * x| := by nlinarith
    calc
      ‖cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I‖ / |s|^2 ≤ (3 * |s * x|) / |s|^2 := by
        gcongr
      _ = 3 * |x| / |s| := by
        rw [abs_mul]
        field_simp [hsabs.ne']
      _ ≤ 3 * x^2 := by
        have hxpos : 0 < |x| := by
          by_contra hx
          push_neg at hx
          have : |s * x| = 0 := by simp [abs_mul, le_antisymm hx (abs_nonneg x)]
          linarith
        have hlt : 1 / |s| < |x| := by
          rw [div_lt_iff₀ hsabs]
          simpa [abs_mul, mul_comm] using hz
        calc
          3 * |x| / |s| = 3 * (|x| * (1 / |s|)) := by field_simp [hsabs.ne']
          _ ≤ 3 * (|x| * |x|) := by gcongr
          _ = 3 * x^2 := by rw [← sq_abs]; ring



theorem charFun_centered_taylor {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h2 : MemLp (fun x : ℝ => x) 2 ν) (hmean : ∫ x, x ∂ν = 0) :
    Tendsto (fun s : ℝ => (charFun ν s - 1) / (s : ℂ) ^ 2) (𝓝[≠] (0:ℝ))
      (𝓝 (-((∫ x, x^2 ∂ν : ℝ) : ℂ) / 2)) := by
  have hint : Integrable (fun x : ℝ => x) ν := memLp_two_integrable h2
  have hsq : Integrable (fun x : ℝ => x^2) ν := h2.integrable_sq
  let F : ℝ → ℝ → ℂ := fun s x => (cexp ((s * x : ℂ) * I) - 1 - (s * x : ℂ) * I) / (s : ℂ)^2
  have hF_meas : ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ), AEStronglyMeasurable (F s) ν := by
    filter_upwards with s
    fun_prop
  have hbound : ∀ᶠ s : ℝ in 𝓝[≠] (0:ℝ), ∀ᵐ x ∂ν, ‖F s x‖ ≤ 3 * x^2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with x
    exact norm_exp_linear_error_div_sq_le x hs
  have hbound_int : Integrable (fun x : ℝ => 3 * x^2) ν := hsq.const_mul 3
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun s : ℝ => F s x) (𝓝[≠] (0:ℝ)) (𝓝 (-(x:ℂ)^2 / 2)) :=
    ae_of_all _ fun x => exp_linear_error_tendsto x
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[≠] (0:ℝ))
    (F := F) (f := fun x : ℝ => -(x:ℂ)^2 / 2) (bound := fun x : ℝ => 3 * x^2)
    hF_meas hbound hbound_int hlim
  have hlimint : ∫ x : ℝ, -(x:ℂ)^2 / 2 ∂ν = -((∫ x, x^2 ∂ν : ℝ) : ℂ) / 2 := by
    have h1 : (fun x : ℝ => -(x:ℂ)^2 / 2) = fun x : ℝ => (-1/2 : ℂ) * (x:ℂ)^2 := by
      ext x; ring
    calc
      ∫ x : ℝ, -(x:ℂ)^2 / 2 ∂ν = (-1/2 : ℂ) * ∫ x : ℝ, (x:ℂ)^2 ∂ν := by
        rw [h1]
        exact integral_const_mul _ _
      _ = (-1/2 : ℂ) * ((∫ x, x^2 ∂ν : ℝ) : ℂ) := by
        have h2 : (fun x : ℝ => (x:ℂ)^2) = fun x : ℝ => ((x^2 : ℝ) : ℂ) := by
          ext x; push_cast; ring
        rw [h2]
        rw [show ∫ x : ℝ, ((x^2 : ℝ) : ℂ) ∂ν = ((∫ x, x^2 ∂ν : ℝ) : ℂ) from integral_complex_ofReal]
      _ = -((∫ x, x^2 ∂ν : ℝ) : ℂ) / 2 := by ring
  rw [hlimint] at hconv
  refine hconv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hexp_int : Integrable (fun x : ℝ => cexp ((s * x : ℂ) * I)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    simp [Complex.norm_exp]
  have hxc : Integrable (fun x : ℝ => (x : ℂ)) ν := hint.ofReal
  have hz_int : Integrable (fun x : ℝ => ((s * x : ℂ) * I) / (s : ℂ)^2) ν := by
    have h := hxc.const_mul (((s : ℂ) * I) / (s : ℂ)^2)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hz_zero : ∫ x : ℝ, ((s * x : ℂ) * I) / (s : ℂ)^2 ∂ν = 0 := by
    have hz_eq : (fun x : ℝ => ((s * x : ℂ) * I) / (s : ℂ)^2) =
        fun x : ℝ => (((s : ℂ) * I) / (s : ℂ)^2) * (x : ℂ) := by
      ext x; ring
    calc
      ∫ x : ℝ, ((s * x : ℂ) * I) / (s : ℂ)^2 ∂ν =
          (((s : ℂ) * I) / (s : ℂ)^2) * ∫ x : ℝ, (x:ℂ) ∂ν := by
        rw [hz_eq]
        exact integral_const_mul _ _
      _ = 0 := by
        rw [show ∫ x : ℝ, (x:ℂ) ∂ν = ((∫ x, x ∂ν : ℝ) : ℂ) from integral_complex_ofReal, hmean]
        simp
  symm
  calc
    (charFun ν s - 1) / (s : ℂ) ^ 2
        = ((∫ x, cexp ((s * x : ℂ) * I) ∂ν) - 1) / (s : ℂ) ^ 2 := by
          rw [charFun_apply_real]
    _ = ((∫ x, cexp ((s * x : ℂ) * I) ∂ν) - ∫ x, (1:ℂ) ∂ν) / (s : ℂ) ^ 2 := by
          rw [integral_const, probReal_univ]
          simp
    _ = (∫ x, (cexp ((s * x : ℂ) * I) - 1) ∂ν) / (s : ℂ) ^ 2 := by
          rw [integral_sub hexp_int (integrable_const _)]
    _ = ∫ x, (cexp ((s * x : ℂ) * I) - 1) / (s : ℂ) ^ 2 ∂ν := by
          exact (integral_div ((s : ℂ) ^ 2) (fun x : ℝ => cexp ((s * x : ℂ) * I) - 1)).symm
    _ = ∫ x, ((cexp ((s * x : ℂ) * I) - 1) / (s : ℂ) ^ 2 -
          ((s * x : ℂ) * I) / (s : ℂ)^2) ∂ν + ∫ x, ((s * x : ℂ) * I) / (s : ℂ)^2 ∂ν := by
          have hA : Integrable (fun x : ℝ => (cexp ((s * x : ℂ) * I) - 1) / (s : ℂ)^2) ν :=
            (hexp_int.sub (integrable_const _)).div_const ((s : ℂ)^2)
          rw [integral_sub hA hz_int]
          ring
    _ = ∫ x, F s x ∂ν := by
          rw [hz_zero, add_zero]
          apply integral_congr_ae
          filter_upwards with x
          simp only [F]
          field_simp [hs0]
end HDP
