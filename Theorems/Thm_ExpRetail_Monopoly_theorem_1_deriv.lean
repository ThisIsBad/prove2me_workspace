import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_1_deriv (P : Params) (hP : P.Standing) :
    ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt (optProfit P) d (Set.Ici 0) 0 := by sorry

end ExpRetail.Monopoly

