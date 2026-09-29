import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: "`C` decreases at every step". If `(c_kl)` is symmetric, the labels
are consistent and every basic restricted variable is strictly positive in the associated
solution (the ε-perturbation device, p. 174), then one step of the iteration strictly decreases
the value `c_00` of `C` in the associated solution. -/
theorem cost_decreases {n N : ℕ} (T T' : Tableau n N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hstep : BealeStep T T') :
    T'.c 0 0 < T.c 0 0 := by sorry

end BealeConvexMin.QuadSimplex
