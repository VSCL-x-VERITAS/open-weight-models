import Mathlib

open scoped BigOperators

namespace HDP.Crosspolytope

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def vertex {n : ℕ} (p : Fin n × Bool) : Space n :=
  (if p.2 then (1/2 : ℝ) else -(1/2 : ℝ)) • EuclideanSpace.single p.1 (1 : ℝ)

noncomputable def vertices (n : ℕ) : Finset (Space n) := by
  classical
  exact Finset.univ.image vertex

noncomputable def body (n : ℕ) : Set (Space n) :=
  convexHull ℝ (vertices n : Set (Space n))

noncomputable def l1Norm {n : ℕ} (x : Space n) : ℝ := ∑ i, |x i|

@[simp] theorem vertex_apply {n : ℕ} (p : Fin n × Bool) (i : Fin n) :
    vertex p i = if i = p.1 then (if p.2 then (1/2 : ℝ) else -(1/2 : ℝ)) else 0 := by
  change (if p.2 then (1/2 : ℝ) else -(1/2 : ℝ)) *
    Pi.single (M := fun _ : Fin n => ℝ) p.1 (1 : ℝ) i = _
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

@[simp] theorem norm_vertex {n : ℕ} (p : Fin n × Bool) : ‖vertex p‖ = 1/2 := by
  rcases p with ⟨i, b⟩
  cases b <;> norm_num [vertex, norm_smul]

theorem vertex_injective (n : ℕ) : Function.Injective (@vertex n) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hi := congrArg (fun x : Space n => x i) h
  have hij : i = j := by
    by_contra hn
    cases b <;> cases c <;> norm_num [vertex_apply, hn] at hi
  subst j
  have hbc : b = c := by
    cases b <;> cases c <;> first | rfl | norm_num [vertex_apply] at hi
  simp [hbc]

theorem card_vertices (n : ℕ) : (vertices n).card = 2 * n := by
  classical
  simp [vertices, Finset.card_image_of_injective _ (vertex_injective n), Nat.mul_comm]

theorem vertex_mem_vertices {n : ℕ} (p : Fin n × Bool) : vertex p ∈ vertices n := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

theorem norm_mem_vertices {n : ℕ} {x : Space n} (hx : x ∈ vertices n) : ‖x‖ = 1/2 := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
  exact norm_vertex p

theorem dist_vertices_le_one {n : ℕ} {x y : Space n}
    (hx : x ∈ vertices n) (hy : y ∈ vertices n) : dist x y ≤ 1 := by
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ = 1 := by rw [norm_mem_vertices hx, norm_mem_vertices hy]; norm_num

theorem norm_body_le_half {n : ℕ} {x : Space n} (hx : x ∈ body n) : ‖x‖ ≤ 1/2 := by
  have hs : (vertices n : Set (Space n)) ⊆ Metric.closedBall 0 (1/2 : ℝ) := by
    intro y hy
    simp [Metric.mem_closedBall, dist_zero_right, norm_mem_vertices hy]
  have h := convexHull_min hs (convex_closedBall (0 : Space n) (1/2 : ℝ)) hx
  simpa [Metric.mem_closedBall, dist_zero_right] using h

theorem dist_body_le_one {n : ℕ} {x y : Space n}
    (hx : x ∈ body n) (hy : y ∈ body n) : dist x y ≤ 1 := by
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 1 := by linarith [norm_body_le_half hx, norm_body_le_half hy]

@[simp] theorem l1Norm_vertex {n : ℕ} (p : Fin n × Bool) : l1Norm (vertex p) = 1/2 := by
  classical
  rcases p with ⟨i, b⟩
  cases b <;> simp [l1Norm, vertex_apply, apply_ite abs]

theorem convex_l1Ball (n : ℕ) : Convex ℝ {x : Space n | l1Norm x ≤ 1/2} := by
  intro x hx y hy a b ha hb hab
  have hle : l1Norm (a • x + b • y) ≤ a * l1Norm x + b * l1Norm y := by
    simp only [l1Norm, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      ∑ i, |a * x i + b * y i| ≤ ∑ i, (a * |x i| + b * |y i|) := by
        apply Finset.sum_le_sum
        intro i _
        simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
          (abs_add_le (a * x i) (b * y i))
      _ = a * ∑ i, |x i| + b * ∑ i, |y i| := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
  change l1Norm (a • x + b • y) ≤ 1/2
  calc
    l1Norm (a • x + b • y) ≤ a * l1Norm x + b * l1Norm y := hle
    _ ≤ a * (1/2) + b * (1/2) := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = 1/2 := by linarith

theorem l1Norm_le_half_of_mem_body {n : ℕ} {x : Space n}
    (hx : x ∈ body n) : l1Norm x ≤ 1/2 := by
  apply convexHull_min (t := {x : Space n | l1Norm x ≤ 1/2}) ?_ (convex_l1Ball n) hx
  intro y hy
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy
  exact (l1Norm_vertex p).le

theorem vertex_mem_body {n : ℕ} (p : Fin n × Bool) : vertex p ∈ body n :=
  subset_convexHull ℝ _ (vertex_mem_vertices p)

theorem zero_mem_body {n : ℕ} (hn : 1 ≤ n) : (0 : Space n) ∈ body n := by
  let i : Fin n := ⟨0, hn⟩
  have h := (convex_convexHull ℝ (vertices n : Set (Space n)))
    (vertex_mem_body (i, true)) (vertex_mem_body (i, false))
    (show 0 ≤ (1/2 : ℝ) by norm_num) (show 0 ≤ (1/2 : ℝ) by norm_num)
    (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  convert h using 1
  simp [vertex, smul_neg]

theorem mem_body_of_l1Norm_le_half {n : ℕ} (hn : 1 ≤ n) {x : Space n}
    (hx : l1Norm x ≤ 1/2) : x ∈ body n := by
  classical
  let w : Option (Fin n) → ℝ := fun o => match o with
    | none => 1 - 2 * l1Norm x
    | some i => 2 * |x i|
  let z : Option (Fin n) → Space n := fun o => match o with
    | none => 0
    | some i => vertex (i, decide (0 ≤ x i))
  have hw : ∀ o ∈ Finset.univ, 0 ≤ w o := by
    intro o _
    cases o with
    | none => dsimp [w]; linarith
    | some i => exact mul_nonneg (by norm_num) (abs_nonneg _)
  have hsum : ∑ o, w o = 1 := by
    simp [w, Fintype.sum_option, l1Norm, ← Finset.mul_sum]
  have hz : ∀ o ∈ Finset.univ, z o ∈ body n := by
    intro o _
    cases o with
    | none => exact zero_mem_body hn
    | some i => exact vertex_mem_body _
  have hcombo : ∑ o, w o • z o = x := by
    ext j
    simp only [Fintype.sum_option, w, z, smul_zero, zero_add,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, vertex_apply]
    rw [Finset.sum_eq_single j]
    · by_cases hj : 0 ≤ x j
      · simp [hj, abs_of_nonneg hj]
        ring
      · simp [hj, abs_of_neg (lt_of_not_ge hj)]
        ring
    · intro i _ hij
      simp [Ne.symm hij]
    · simp
  rw [← hcombo]
  exact (convex_convexHull ℝ (vertices n : Set (Space n))).sum_mem hw hsum hz

theorem body_eq_l1Ball {n : ℕ} (hn : 1 ≤ n) :
    body n = {x | l1Norm x ≤ 1/2} := by
  ext x
  exact ⟨l1Norm_le_half_of_mem_body, mem_body_of_l1Norm_le_half hn⟩

theorem extremePoints_body (n : ℕ) :
    (body n).extremePoints ℝ = (vertices n : Set (Space n)) := by
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  intro x hx
  refine mem_extremePoints_iff_left.mpr ⟨subset_convexHull ℝ _ hx, ?_⟩
  intro y hy z hz hseg
  by_cases hyz : y = z
  · subst z
    have hxy : x = y := by simpa only [openSegment_same, Set.mem_singleton_iff] using hseg
    exact hxy.symm
  · have hyn : y ∈ Metric.closedBall (0 : Space n) (1/2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using norm_body_le_half hy
    have hzn : z ∈ Metric.closedBall (0 : Space n) (1/2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using norm_body_le_half hz
    have hlt := openSegment_subset_ball_of_ne hyn hzn hyz hseg
    have hnorm := norm_mem_vertices hx
    simp [Metric.mem_ball, dist_zero_right, hnorm] at hlt

end HDP.Crosspolytope
