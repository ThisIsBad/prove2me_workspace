import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, proof of (2), p. 114: with prices `π¹ > π² > ⋯ > πᵖ > 0` on the goods of the cycles
`S¹, …, Sᵖ`, the item of a trader's cyclic successor costs exactly what his own item sells for,
and every item he can afford lies in his own cycle or a later one. -/
theorem affordable_iff_later_stage {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) (π : Fin P.p → ℝ) (hπ : StrictAnti π)
    (hπpos : ∀ j, 0 < π j) (i : N) :
    π (P.stage (P.next i)) = π (P.stage i) ∧
      ∀ k, π (P.stage k) ≤ π (P.stage i) → P.stage i ≤ P.stage k := by sorry

end ShapleyScarf.TopTrading

