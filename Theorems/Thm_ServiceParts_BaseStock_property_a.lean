import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Property (a) in the proof of Theorem 2, p. 18 (sₙ* ≥ sₙ₋₁*): for n ≥ 2, if the
order-up-to rule with level s is optimal in the n-period problem and the order-up-to rule
with level s' is optimal in the (n + 1)-period problem, then s ≤ s'. -/
theorem property_a (M : Model) (n : ℕ) (hn : 2 ≤ n) (s s' : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (hs' : M.IsOrderUpToOptimal (n + 1) s') : s ≤ s' := by sorry

end ServiceParts.BaseStock

