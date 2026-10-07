import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.17), p. 110: under (4.12), with `k = a²/b`,
`exp(−δ²k/8) < 1/(8k)`. -/
theorem ineq_4_17 (δ a b : ℝ) (hpar : ParamConditions δ a b) :
    Real.exp (-(δ ^ 2 * kStar a b / 8)) < 1 / (8 * kStar a b) := by sorry

end FreedmanTail.LowerTail

