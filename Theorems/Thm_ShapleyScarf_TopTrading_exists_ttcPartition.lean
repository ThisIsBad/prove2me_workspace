import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, p. 114: every market has a top-trading-cycle partition `N = S¹ ∪ ⋯ ∪ Sᵖ`. -/
theorem exists_ttcPartition {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) :
    Nonempty (TTCPartition A) := by sorry

end ShapleyScarf.TopTrading

