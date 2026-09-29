import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
import Definitions.Def_MasekPaterson_Shared_steps
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Theorem 5, pinned to what its proof establishes: in the example, the horizontal steps
`δ_{k,k+1} - δ_{k,k}` (`k = 0, 1, 2, …`) are pairwise distinct, so the edit matrix of
`A^n, B^n` has at least `n` distinct steps, and the set of possible steps of the cost
function is infinite. -/
theorem steps_unbounded :
    Function.Injective (fun k : ℕ => exDelta k (k + 1) - exDelta k k) ∧
    ¬ (possibleSteps exCost).Finite := by sorry

end MasekPaterson.Necessity

