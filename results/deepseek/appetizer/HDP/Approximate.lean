/-
The approximate Carathéodory theorem (Theorem 0.0.2), its diameter form
(footnote 1), and the covering corollary for polytopes (Corollary 0.0.4).
-/
import Mathlib
import HDP.FiniteProbability

open Set BigOperators MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace InnerProductSpace
set_option maxHeartbeats 1000000

namespace HDP
theorem centered_approx_sq {n m k : ℕ} (lam : Fin m → ℝ)
    (z : Fin m → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) (D : ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (hx : ∑ i, lam i • z i = x) (hz : ∀ i, ‖z i‖ ≤ D) (hk : 0 < k) :
    ∃ ω : Fin k → Fin m, ‖x - (1 / (k:ℝ)) • ∑ j, z (ω j)‖ ^ 2 ≤ D ^ 2 / (k:ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp at hlam1
  let μ := (weightPMF lam hlam0 hlam1).toMeasure
  let ν := Measure.pi (fun _ : Fin k => μ)
  haveI hμ : IsProbabilityMeasure μ := inferInstance
  haveI hν : IsProbabilityMeasure ν := inferInstance
  let V : ℝ := ∑ i, lam i * ‖z i - x‖ ^ 2
  let W : Fin k → (Fin k → Fin m) → EuclideanSpace ℝ (Fin n) := fun j ω => x - z (ω j)
  have hW : ∀ j, MemLp (W j) 2 ν := fun j => MemLp.of_discrete
  have hind_coord : iIndepFun (fun j (ω : Fin k → Fin m) => ω j) ν := by
    exact iIndepFun_pi (μ := fun _ : Fin k => μ) (X := fun _ : Fin k => id)
      (fun _ => aemeasurable_id)
  have hind : iIndepFun W ν := by
    have := hind_coord.comp (fun _ : Fin k => fun u : Fin m => x - z u)
      (fun _ => measurable_of_finite _)
    simpa [W, Function.comp_def] using this
  have hmeanW : ∀ j, ∫ ω, W j ω ∂ν = 0 := by
    intro j
    have hmarg : ∫ ω, W j ω ∂ν = ∫ a, (x - z a) ∂μ := by
      simpa [W] using marginal_integral (E := EuclideanSpace ℝ (Fin n)) lam hlam0 hlam1
        (fun a => x - z a) j
    calc
      ∫ ω, W j ω ∂ν = ∫ a, (x - z a) ∂μ := hmarg
      _ = x - ∫ a, z a ∂μ := by
        rw [integral_sub (integrable_const x) (Integrable.of_finite)]
        simp
      _ = x - x := by
        rw [integral_weightPMF]
        simp [hx]
      _ = 0 := sub_self x
  have hVj : ∀ j, ∫ ω, ‖W j ω‖ ^ 2 ∂ν = V := by
    intro j
    calc
      ∫ ω, ‖W j ω‖ ^ 2 ∂ν = ∫ a, ‖x - z a‖ ^ 2 ∂μ := by
        simpa [W] using marginal_integral (E := ℝ) lam hlam0 hlam1 (fun a => ‖x - z a‖ ^ 2) j
      _ = ∑ i, lam i * ‖x - z i‖ ^ 2 := by
        rw [integral_weightPMF]
        simp [smul_eq_mul]
      _ = V := by
        dsimp [V]
        simp [norm_sub_rev]
  have hVle : V ≤ D ^ 2 := by
    have hvar := weighted_variance_identity lam z x hlam1 hx
    have hzle : ∑ i, lam i * ‖z i‖ ^ 2 ≤ ∑ i, lam i * D ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hz i) 2) (hlam0 i)
    have hzle' : ∑ i, lam i * ‖z i‖ ^ 2 ≤ D ^ 2 := by
      rw [← Finset.sum_mul] at hzle
      simpa [hlam1] using hzle
    have hxnonneg : 0 ≤ ‖x‖ ^ 2 := by positivity
    dsimp [V]
    linarith
  have hInt : ∫ ω, ‖x - (1 / (k:ℝ)) • ∑ j, z (ω j)‖ ^ 2 ∂ν = V / (k:ℝ) := by
    have hdecomp : ∀ ω, x - (1 / (k:ℝ)) • ∑ j, z (ω j) = (1 / (k:ℝ)) • ∑ j, W j ω := by
      intro ω
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ k x]
      rw [smul_sub, smul_smul, one_div, inv_mul_cancel₀ (by positivity : (k:ℝ) ≠ 0), one_smul]
    have hsq : ∀ ω, ‖x - (1 / (k:ℝ)) • ∑ j, z (ω j)‖ ^ 2 =
        (1 / (k:ℝ)) ^ 2 * ‖∑ j, W j ω‖ ^ 2 := by
      intro ω
      rw [hdecomp ω, norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    calc
      ∫ ω, ‖x - (1 / (k:ℝ)) • ∑ j, z (ω j)‖ ^ 2 ∂ν
          = ∫ ω, (1 / (k:ℝ)) ^ 2 * ‖∑ j, W j ω‖ ^ 2 ∂ν := by
            simp_rw [hsq]
      _ = (1 / (k:ℝ)) ^ 2 * ∫ ω, ‖∑ j, W j ω‖ ^ 2 ∂ν :=
            integral_const_mul _ _
      _ = (1 / (k:ℝ)) ^ 2 * ∑ j, ∫ ω, ‖W j ω‖ ^ 2 ∂ν := by
            rw [integral_norm_sq_sum_of_indep_mean_zero W hW hind hmeanW]
      _ = (1 / (k:ℝ)) ^ 2 * ((k:ℝ) * V) := by
            simp [hVj, Finset.sum_const, nsmul_eq_mul]
      _ = V / (k:ℝ) := by
            field_simp
  have hsum : ∑ ω : Fin k → Fin m, (∏ i, lam (ω i)) * ‖x - (1 / (k:ℝ)) • ∑ j, z (ω j)‖ ^ 2
      ≤ V / (k:ℝ) := by
    rw [← product_integral_weight]
    exact hInt.le
  have hWsum : ∑ ω : Fin k → Fin m, (∏ i, lam (ω i)) = 1 := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin m)))
      (g := fun (_ : Fin k) (i : Fin m) => lam i)
    simpa [hlam1] using h
  have hW0 : ∀ ω : Fin k → Fin m, 0 ≤ ∏ i, lam (ω i) :=
    fun ω => Finset.prod_nonneg fun i _ => hlam0 (ω i)
  obtain ⟨ω, hω⟩ := exists_le_of_sum_mul_le hW0 hWsum hsum
  refine ⟨ω, hω.trans ?_⟩
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  calc
    V / (k:ℝ) ≤ D ^ 2 / (k:ℝ) := by gcongr

theorem approximate_caratheodory {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)}
    (hbdd : Bornology.IsBounded T) {D : ℝ} (hD : 0 ≤ D) (hdiam : Metric.diam T ≤ D)
    (hx : x ∈ convexHull ℝ T) {k : ℕ} (hk : 0 < k) :
    ∃ y : Fin k → EuclideanSpace ℝ (Fin n), (∀ j, y j ∈ T) ∧
      ‖x - (1 / (k:ℝ)) • ∑ j, y j‖ ≤ D / Real.sqrt k := by
  have hpair : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ D := by
    intro s hs t ht
    have h := Metric.dist_le_diam_of_mem hbdd hs ht
    have h' : dist s t ≤ D := h.trans hdiam
    simpa [dist_eq_norm] using h'
  rw [mem_convexHull_iff_exists_fintype] at hx
  obtain ⟨ι, hι, lam, z, hlam0, hlam1, hzT, hxsum⟩ := hx
  letI : Fintype ι := hι
  let m := Fintype.card ι
  let e := Fintype.equivFin ι
  let lam' : Fin m → ℝ := fun i => lam (e.symm i)
  let z' : Fin m → EuclideanSpace ℝ (Fin n) := fun i => z (e.symm i)
  have hlam0' : ∀ i, 0 ≤ lam' i := fun i => hlam0 _
  have hlam1' : ∑ i, lam' i = 1 := by
    dsimp [lam']
    rw [Equiv.sum_comp e.symm lam, hlam1]
  have hx' : ∑ i, lam' i • z' i = x := by
    dsimp [lam', z']
    rw [Equiv.sum_comp e.symm (fun i => lam i • z i), hxsum]
  have hzT' : ∀ i, z' i ∈ T := fun i => hzT _
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI := h
    simp at hlam1
  have hm : 0 < m := by
    dsimp [m]
    exact Fintype.card_pos_iff.mpr hne
  let i0 : Fin m := ⟨0, hm⟩
  let z0 : EuclideanSpace ℝ (Fin n) := z' i0
  have hz'' : ∀ i, ‖z' i - z0‖ ≤ D := fun i => hpair (z' i) (hzT' i) z0 (hzT' i0)
  have hx'' : ∑ i, lam' i • (z' i - z0) = x - z0 := by
    calc
      ∑ i, lam' i • (z' i - z0) = ∑ i, (lam' i • z' i - lam' i • z0) := by
        simp [smul_sub]
      _ = ∑ i, lam' i • z' i - ∑ i, lam' i • z0 := by rw [Finset.sum_sub_distrib]
      _ = x - (∑ i, lam' i) • z0 := by rw [hx', Finset.sum_smul]
      _ = x - z0 := by rw [hlam1', one_smul]
  obtain ⟨ω, hω⟩ := centered_approx_sq lam' (fun i => z' i - z0) (x - z0) D
    hlam0' hlam1' hx'' hz'' hk
  let y : Fin k → EuclideanSpace ℝ (Fin n) := fun j => z' (ω j)
  have hyT : ∀ j, y j ∈ T := fun j => hzT' (ω j)
  have hsq : ‖x - (1 / (k:ℝ)) • ∑ j, y j‖ ^ 2 ≤ D ^ 2 / (k:ℝ) := by
    have hdecomp : x - (1 / (k:ℝ)) • ∑ j, z' (ω j) =
        (x - z0) - (1 / (k:ℝ)) • ∑ j, (z' (ω j) - z0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ k z0]
      rw [smul_sub, smul_smul]
      have hk' : (k:ℝ) ≠ 0 := by positivity
      field_simp [hk']
      module
    have hsum_sub : ∑ j, (z' (ω j) - z0) = ∑ j, z' (ω j) - k • z0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hω' : ‖(x - z0) - (1 / (k:ℝ)) • ∑ j, (z' (ω j) - z0)‖ ^ 2 ≤ D ^ 2 / (k:ℝ) := by
      simpa only [← hsum_sub] using hω
    dsimp [y]
    rw [hdecomp]
    exact hω'
  refine ⟨y, hyT, ?_⟩
  have hsqrt : ‖x - (1 / (k:ℝ)) • ∑ j, y j‖ ≤ Real.sqrt (D ^ 2 / (k:ℝ)) :=
    Real.le_sqrt_of_sq_le hsq
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hDnonneg : 0 ≤ D := hD
  have hsqrt_eq : Real.sqrt (D ^ 2 / (k:ℝ)) = D / Real.sqrt k := by
    rw [Real.sqrt_div' (D ^ 2) (le_of_lt hkpos), Real.sqrt_sq hDnonneg]
  rwa [hsqrt_eq] at hsqrt

lemma inv_sqrt_ceil_le {ε : ℝ} (hε : 0 < ε) :
    1 / Real.sqrt (Nat.ceil (1 / ε ^ 2) : ℝ) ≤ ε := by
  have hkpos : (0:ℝ) < (Nat.ceil (1 / ε ^ 2) : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr (by positivity)
  have hle : 1 / ε ^ 2 ≤ (Nat.ceil (1 / ε ^ 2) : ℝ) := Nat.le_ceil _
  have hsqrt : 1 / ε ≤ Real.sqrt (Nat.ceil (1 / ε ^ 2) : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / ε)]
    apply Real.sqrt_le_sqrt
    simpa [one_div, inv_pow] using hle
  have hpos : (0:ℝ) < 1 / ε := by positivity
  have h := one_div_le_one_div_of_le hpos hsqrt
  simpa [one_div] using h

theorem covering_polytope {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hbdd : Bornology.IsBounded (s : Set (EuclideanSpace ℝ (Fin n))))
    (hdiam : Metric.diam (s : Set (EuclideanSpace ℝ (Fin n))) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
      C.card ≤ s.card ^ Nat.ceil (1 / ε ^ 2) ∧
      ∀ x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))),
        ∃ c ∈ C, dist x c ≤ ε := by
  let k := Nat.ceil (1 / ε ^ 2)
  have hk : 0 < k := Nat.ceil_pos.mpr (by positivity)
  by_cases hne : s.Nonempty
  · let C : Finset (EuclideanSpace ℝ (Fin n)) :=
      Finset.univ.image (fun y : Fin k → s =>
        (1 / (k:ℝ)) • ∑ j, (y j : EuclideanSpace ℝ (Fin n)))
    refine ⟨C, ?_, ?_⟩
    · calc
        C.card ≤ Fintype.card (Fin k → s) := Finset.card_image_le
        _ = Fintype.card s ^ Fintype.card (Fin k) := Fintype.card_fun
        _ = s.card ^ k := by simp [Fintype.card_coe]
    · intro x hx
      obtain ⟨y, hyT, hdist⟩ := approximate_caratheodory (T := (s : Set (EuclideanSpace ℝ (Fin n))))
        (x := x) hbdd (D := 1) (by norm_num) (by simpa using hdiam) hx hk
      let y' : Fin k → s := fun j => ⟨y j, hyT j⟩
      refine ⟨(1 / (k:ℝ)) • ∑ j, (y' j : EuclideanSpace ℝ (Fin n)),
        Finset.mem_image.mpr ⟨y', Finset.mem_univ _, rfl⟩, ?_⟩
      have hle : 1 / Real.sqrt (k:ℝ) ≤ ε := inv_sqrt_ceil_le hε
      calc
        dist x ((1 / (k:ℝ)) • ∑ j, (y' j : EuclideanSpace ℝ (Fin n)))
            = ‖x - (1 / (k:ℝ)) • ∑ j, y j‖ := by
              simp [y', dist_eq_norm]
        _ ≤ 1 / Real.sqrt (k:ℝ) := hdist
        _ ≤ ε := hle
  · have hempty : (s : Set (EuclideanSpace ℝ (Fin n))) = ∅ := by
      rw [← Finset.coe_empty, Finset.coe_inj]
      exact Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, ?_, ?_⟩
    · simp
    · intro x hx
      simp [hempty] at hx

end HDP
