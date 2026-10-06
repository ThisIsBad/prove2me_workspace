import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "it can never return to a standard form with the same set of
restricted nonbasic variables, even with a different set of free nonbasic variables". Along a
finite run `T 0 → T 1 → ⋯ → T j` of the iteration, started from a symmetric `(c_kl)` with positive
semidefinite quadratic block and consistent labels, with every basic restricted variable strictly
positive at every tableau, two standard-form tableaux `T i`, `T j` with `i < j` have different
sets of restricted nonbasic variables. -/
theorem no_return_standard_form {n N : ℕ} (T : ℕ → Tableau n N) (hsymm : (T 0).c.IsSymm)
    (hpsd : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent (T 0))
    {i j : ℕ} (hij : i < j) (hstep : ∀ k < j, BealeStep (T k) (T (k + 1)))
    (hpos : ∀ k ≤ j, BasicPositive (T k))
    (hi : IsStandardForm (T i)) (hj : IsStandardForm (T j)) :
    restrictedNonbasic (T i) ≠ restrictedNonbasic (T j) := by sorry

end BealeConvexMin.QuadSimplex

