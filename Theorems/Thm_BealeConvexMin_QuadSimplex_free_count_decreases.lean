import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "if `C` is not in standard form and `s = s_0` say, then `s` cannot
increase, and must decrease after at most `s_0` steps, unless `C` meanwhile achieves standard
form". Let `T 0` have a symmetric `(c_kl)`, not be in standard form, and have `s_0 = numFree (T 0)`
nonbasic free variables, and let `T 0 → T 1 → ⋯ → T s_0` be steps of the iteration. Then some
`i ≤ s_0` has `T i` in standard form or `s(T i) < s_0`, and `s(T i') ≤ s_0` for all `i' ≤ i`. -/
theorem free_count_decreases {n N : ℕ} (T : ℕ → Tableau n N) (hsymm : (T 0).c.IsSymm)
    (hns : ¬ IsStandardForm (T 0))
    (hstep : ∀ k < numFree (T 0), BealeStep (T k) (T (k + 1))) :
    ∃ i ≤ numFree (T 0), (IsStandardForm (T i) ∨ numFree (T i) < numFree (T 0)) ∧
      ∀ i' ≤ i, numFree (T i') ≤ numFree (T 0) := by sorry

end BealeConvexMin.QuadSimplex
