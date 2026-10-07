import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop
import Definitions.Def_FlowJobShop_PairGroups_AlgorithmH

namespace FlowJobShop.PairGroups

open FlowShop

/-- §2, description of algorithm H (p. 48): for every group `g` of at most two processors, the
flow shop on that group has an optimal finish time schedule (the paper obtains it with
Johnson's algorithm). -/
theorem optimal_group_schedules_exist {m n : ℕ} (F : FlowShop m n) (g : Fin ((m + 1) / 2)) :
    ∃ ρ : Fin (groupSize m g) → Fin n → ℝ, (F.group g).IsOptimal ρ := by sorry

end FlowJobShop.PairGroups

