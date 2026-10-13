import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- §2.2, p. 337: shifting a balanced final block until the first stopping
event leaves total discrepancy unchanged. -/
theorem shift_cost_eq (a l s : ℕ → ℝ) (m j : ℕ) (δ : ℝ)
    (hfeas : FixedFeasible l (m + 1) s)
    (hblock : IsBlock l (m + 1) s j m)
    (hbalance : decCount a s j m = incCount a s j m)
    (hpositive : s j ≠ 0)
    (hδ : 0 ≤ δ ∧ δ ≤ shiftAmount a l s j m) :
    cost a (m + 1) (shiftRange s j m δ) = cost a (m + 1) s := by sorry

end GTWSched.FixedOrder

