import Mathlib
import Definitions.Def_BellmanDP_Games_MinMax

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 7, p. 308 (the extended min-max theorem).
If `Σ_{i,j} b_ij p_i q_j ≥ d > 0` for all distribution vectors `p` and `q`, then
`Max_p Min_q (Σ a_ij p_i q_j)/(Σ b_ij p_i q_j) = Min_q Max_p (Σ a_ij p_i q_j)/(Σ b_ij p_i q_j)`:
both extrema exist and are equal. Distribution vectors are the points of the standard simplices;
the index types are nonempty (`p = (p_1, …, p_M)` with `M ≥ 1`, `q = (q_1, …, q_N)` with
`N ≥ 1`, § 2). -/
theorem extended_min_max {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ ι, ∀ q ∈ stdSimplex ℝ κ, d ≤ bilin B p q) :
    ∃ v : ℝ, IsMaxMinMinMaxValue (fun p q => bilin A p q / bilin B p q)
      (stdSimplex ℝ ι) (stdSimplex ℝ κ) v := by sorry

end BellmanDP.Games

