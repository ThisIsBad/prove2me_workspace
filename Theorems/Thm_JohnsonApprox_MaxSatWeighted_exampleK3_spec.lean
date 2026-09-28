import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2
import Definitions.Def_JohnsonApprox_MaxSatWeighted_ExampleK3

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 264), the lower-bound input for `k = 3`: it is an input of `MS(3)`,
`S* = 8`, and B2 has a choosable output with `7` clauses, so `r(B2, S) = 8/7`. -/
theorem exampleK3_spec :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 8 ∧ ∃ X, Choosable exampleK3 X ∧ X.card = 7 := by sorry

end JohnsonApprox.MaxSatWeighted

