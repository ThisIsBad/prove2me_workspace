import Mathlib
import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem disruption_stationary (α β : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Summable (disruptionPmf α β) ∧ (∑' n, disruptionPmf α β n) = 1
      ∧ IsStationary α β (disruptionPmf α β)
      ∧ ∀ n, disruptionCdf α β n = 1 - α / (α + β) * (1 - β) ^ n := by sorry

end SupplyChainTheory
