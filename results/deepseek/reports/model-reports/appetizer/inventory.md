# Source inventory and coverage

Source: `source/Appetizer.pdf` (4 pages), SHA-256
`164189f2c6e5d39c6b8aa96f3a3c18d02f42194b890be3610aaa44d7c487ca7f`.
Mathematical items below are the complete inventory derived from the extracted
text; page numbers are PDF pages.

## Definitions and displayed formulas

| Item | Source location | Lean item | Status |
|---|---|---|---|
| Convex combination (0.1): `Σ λᵢ zᵢ`, `λᵢ ≥ 0`, `Σ λᵢ = 1` | p. 1, eq. (0.1) | `HDP.IsConvexCombination` | formalized |
| `conv(T)` = all finite convex combinations of points of `T` | p. 1 | `HDP.mem_convexHull_iff_exists_convexCombination` | formalized (identified with Mathlib `convexHull`) |
| Diameter `diam(T) = sup {‖s−t‖₂}` | p. 2, footnote 1 | `HDP.diameter`, `HDP.DiameterLe` | formalized as definitions; main theorems use the equivalent pairwise-distance hypothesis or `Metric.diam` |

## Numbered results

| Item | Source location | Lean item | Status |
|---|---|---|---|
| Theorem 0.0.1 (Carathéodory): every point of `conv(T) ⊆ ℝⁿ` is a convex combination of at most `n+1` points of `T` | p. 1 | `HDP.caratheodory` | formalized |
| Sharpness of the `n+1` bound: attained for a simplex of `n+1` points in general position | p. 1 | `HDP.caratheodory_bound_sharp` | formalized |
| Theorem 0.0.2 (Approximate Carathéodory), diameter ≤ 1: for every `x ∈ conv(T)` and every integer `k`, points `x₁,…,x_k ∈ T` with `‖x − (1/k)Σx_j‖₂ ≤ 1/√k` | p. 2 | `HDP.approximate_caratheodory` with `D = 1` | formalized (for positive `k`; `k = 0` is not meaningful in the displayed quantity) |
| Footnote 1: for general `T` the bound is `diam(T)/√k` | p. 2 | `HDP.approximate_caratheodory` with general `D` | formalized |
| Exercise 0.0.3(a): independent mean-zero random vectors satisfy `E‖ΣZ_j‖₂² = Σ E‖Z_j‖₂²` | p. 3 | `HDP.integral_norm_sq_sum_of_indep_mean_zero` | formalized for `EuclideanSpace ℝ (Fin n)` with `iIndepFun`, `MemLp`, and zero means |
| Exercise 0.0.3(b): `E‖Z − E Z‖₂² = E‖Z‖₂² − ‖E Z‖₂²` | p. 3 | `HDP.variance_identity_vector` | formalized for a general probability measure and square-integrable random vector |
| Corollary 0.0.4: a polytope with `N` vertices and diameter ≤ 1 is covered by at most `N^⌈1/ε²⌉` Euclidean balls of radius `ε` | p. 4 | `HDP.covering_polytope` | formalized (centers are equal-weight averages of vertices; cardinal bound `s.card^k`) |
| Exercise 0.0.5: `(n/m)^m ≤ C(n,m) ≤ Σ_{k=0}^m C(n,k) ≤ (en/m)^m` for `1 ≤ m ≤ n` | p. 4 | `HDP.sum_choose_bounds` | formalized |
| Exercise 0.0.6: `(C + Cε²N)^⌈1/ε²⌉` balls suffice | p. 4 | `HDP.improved_covering` with `C = 4` | formalized |

## Proof claims and intermediate displays

| Claim | Source location | Lean item | Status |
|---|---|---|---|
| Translation/radius reduction `‖t‖₂ ≤ 1` for `t ∈ T` | p. 2, (0.2) | embedded in `HDP.approximate_caratheodory` (translate by a point `z₀ ∈ T`) | formalized as proof step |
| Probabilistic interpretation `E Z = x` | p. 2 | `HDP.weighted_variance_identity`, `HDP.integral_norm_sq_sum_of_indep_mean_zero` (finite measure construction) | formalized |
| `E‖x − (1/k)ΣZ_j‖₂² = (1/k²)Σ E‖Z_j − x‖₂²` | p. 2 | `HDP.integral_norm_sq_sum_of_indep_mean_zero` plus the scaling step in `HDP.centered_approx_sq` | formalized |
| `E‖Z_j − x‖₂² = E‖Z‖₂² − ‖E Z‖₂² ≤ 1` | p. 3 | `HDP.weighted_variance_identity` | formalized |
| Existence of a realization with the mean-square bound | p. 3 | `HDP.exists_le_of_sum_mul_le` used in `HDP.centered_approx_sq` | formalized |
| Center set `N = {(1/k)Σx_j : x_j vertices of P}` | p. 4 | `HDP.covering_polytope`, `HDP.improved_covering` | formalized |
| `|N| ≤ N^k` for ordered tuples | p. 4 | `HDP.covering_polytope` | formalized |
| `|N| ≤ C(N+k−1,k)` for unordered multisets | p. 4, hint to Exercise 0.0.6 | `HDP.improved_covering` (via `Sym s k` and `Sym.card_sym_eq_choose`) | formalized |

## Narrative and exclusions

| Item | Source location | Reason |
|---|---|---|
| Figures 0.1 and 0.2 | pp. 1, 3 | Illustrations only; no mathematical assertion. |
| Strong law of large numbers sentence | p. 2 | Cited background, used only as motivation; the quantitative variance argument is formalized instead. |
| Discussion of packing, entropy/coding, random processes | p. 4 | Bibliographic pointers to later chapters; no mathematical claim in this section. |
| Notes 0.0.1 and references `[8]`, `[166]`, `[49]`, `[50]` | p. 4 | Historical/bibliographic narrative, no formal mathematical assertion. |
