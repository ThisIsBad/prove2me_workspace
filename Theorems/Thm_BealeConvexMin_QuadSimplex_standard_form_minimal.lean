import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "When `C` is in standard form, its value in the associated solution,
`c_00`, cannot be decreased keeping the nonbasic restricted variables equal to zero." For a
symmetric `(c_kl)` with positive semidefinite quadratic block (convex `C`), in standard form, every
`z` with `z_0 = 1` and `z_k = 0` on the restricted nonbasic slots has `C(z) ≥ c_00`. -/
theorem standard_form_minimal {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) :
    T.c 0 0 ≤ quadValue T.c z := by sorry

end BealeConvexMin.QuadSimplex
