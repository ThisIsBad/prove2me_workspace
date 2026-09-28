import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177, Lemma 1. If the new nonbasic variable is the free variable
`u_r = c_p0 + Σ_l c_pl z_l` of (3.2), i.e. (3.3) has coefficients `d = (c_p0, c_p1, …, c_pN)`
(row `p` of `c`), then `e_q = 1/c_pp`, `e_l = -c_pl/c_pp` for `l ≠ q`, and every off-diagonal entry
of the new row and column (slot `p`, where the paper's `z_q` is stored) vanishes, index `0`
included: `c''_ql = c''_kq = 0` for `k, l ≠ q`. `(c_kl)` is symmetric and `c_pp ≠ 0`. -/
theorem lemma1 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hc : c.IsSymm)
    (p : Fin (N + 1)) (hp : c p p ≠ 0) :
    pivotE (c p) p p = 1 / c p p ∧
    (∀ l, l ≠ p → pivotE (c p) p l = -c p l / c p p) ∧
    ∀ k, k ≠ p → pivotC c p (c p) p k = 0 ∧ pivotC c p (c p) k p = 0 := by sorry

end BealeConvexMin.QuadSimplex
