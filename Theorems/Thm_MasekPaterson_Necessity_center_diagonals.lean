import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Lemma 7: for all `k`, (a) `δ_{k,k} = k - μ_k` and
(b) `δ_{k,k+1} = δ_{k+1,k} = 5 + (μ_{k+1} + μ_k) π`. -/
theorem center_diagonals (k : ℕ) :
    exDelta k k = (k : ℝ) - (mu k : ℝ) ∧
    (exDelta k (k + 1) = exDelta (k + 1) k ∧
      exDelta (k + 1) k = 5 + ((mu (k + 1) : ℝ) + (mu k : ℝ)) * Real.pi) := by sorry

end MasekPaterson.Necessity

