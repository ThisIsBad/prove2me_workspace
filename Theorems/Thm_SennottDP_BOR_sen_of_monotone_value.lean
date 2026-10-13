import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Corollary 7.5.4, p. 144. Let `S = {0, 1, 2, …}` and assume `V_α` is
increasing in `i` for every `α ∈ (0,1)`. If there exists a `0` standard (randomized stationary)
policy, then the (SEN) assumptions hold (for the distinguished state `0`), and every limit function
is nonnegative and increasing in `i`. -/
theorem sen_of_monotone_value {Act : Type} (M : SennottDP.Discounted.MDC ℕ Act)
    (hmono : ∀ α : ℝ, 0 < α → α < 1 → Monotone (valueFn M α))
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy 0) :
    SEN M 0 ∧ ∀ h : ℕ → ℝ, IsLimitFunction M 0 h → (∀ i, 0 ≤ h i) ∧ Monotone h := by sorry

end SennottDP.BOR

