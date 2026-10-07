import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, assertions (1) and (2), p. 114: for every top-trading-cycle partition, the allocation
that gives each trader the item of his cyclic successor is a core allocation, and it is
competitive at the prices `π^{stage k}` for every choice `π¹ > π² > ⋯ > πᵖ > 0`. -/
theorem ttc_core_and_competitive {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) :
    IsCoreAllocation A P.next ∧
      ∀ π : Fin P.p → ℝ, StrictAnti π → (∀ j, 0 < π j) →
        IsCompetitive A P.next (fun k => π (P.stage k)) := by sorry

end ShapleyScarf.TopTrading

