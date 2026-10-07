import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop
import Definitions.Def_FlowJobShop_PairGroups_AlgorithmH

namespace FlowJobShop.PairGroups

open FlowShop

/-- §2, description of algorithm H (p. 48): concatenating feasible schedules `R g` of the group
flow shops, each shifted by `Σ_{h<g} FT(R(h))`, gives a feasible schedule of the original
`m`-processor flow shop. -/
theorem algorithmH_feasible {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsFeasible (R g)) :
    F.IsFeasible (F.algorithmH R) := by sorry

end FlowJobShop.PairGroups

