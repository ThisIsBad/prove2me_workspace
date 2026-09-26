import Mathlib
import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem disruption_optimal_multiple (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) :
    ∃ k : ℕ, IsMinOn (meanCost α β h p d) Set.univ (k * d)
      ∧ ∀ S, IsMinOn (meanCost α β h p d) Set.univ S → k * d ≤ S := by sorry

end SupplyChainTheory
