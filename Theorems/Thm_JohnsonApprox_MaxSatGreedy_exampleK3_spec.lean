import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1
import Definitions.Def_JohnsonApprox_MaxSatGreedy_ExampleK3

namespace JohnsonApprox.MaxSatGreedy

theorem exampleK3_spec :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 4 ∧
      (∃ X, Choosable exampleK3 X ∧ X.card = 3) ∧ (∀ X, Choosable exampleK3 X → 3 ≤ X.card) := by sorry

end JohnsonApprox.MaxSatGreedy

