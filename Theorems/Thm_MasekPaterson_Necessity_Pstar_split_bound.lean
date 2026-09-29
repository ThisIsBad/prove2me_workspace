import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Lemma 6: for all `k'` with `0 ≤ k' ≤ k`,
`P*(0, 0, k') + 5 + P*(k' + 1, k', k - k') ≥ 5 + (μ_{k+1} + μ_k) π`. -/
theorem Pstar_split_bound (k k' : ℕ) (hk' : k' ≤ k) :
    5 + ((mu (k + 1) : ℝ) + (mu k : ℝ)) * Real.pi
      ≤ exPstar 0 0 k' + 5 + exPstar (k' + 1) k' (k - k') := by sorry

end MasekPaterson.Necessity
