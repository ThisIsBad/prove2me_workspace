import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 175, paragraph after (3.1): if no nonbasic variable can profitably be
altered (no free slot with `c_k0 ≠ 0`, no restricted slot with `c_k0 < 0`) and `C` is convex
(symmetric `(c_kl)` whose quadratic block `(c_kl)_{k,l ≥ 1}` is positive semidefinite), then the
associated solution is an absolute minimum: every feasible point `z` (with `z_0 = 1`, every
restricted nonbasic variable `≥ 0` and every restricted variable `x_j = Σ_l row j l · z_l ≥ 0`)
has `C(z) ≥ c_00`. -/
theorem optimality_criterion {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hopt : ∀ k : Fin N, ¬ IsProfitable T k)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → 0 ≤ z k.succ)
    (hrow : ∀ j : Fin n, 0 ≤ ∑ l, T.row j l * z l) :
    T.c 0 0 ≤ quadValue T.c z := by sorry

end BealeConvexMin.QuadSimplex
