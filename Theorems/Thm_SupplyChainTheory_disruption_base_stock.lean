import Mathlib
import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem disruption_base_stock (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (k : ℕ)
    (hk : p / (p + h) ≤ disruptionCdf α β k) (hk' : ∀ n < k, disruptionCdf α β n < p / (p + h)) :
    IsMinOn (meanCost α β h p d) Set.univ (d + d * k)
      ∧ ∀ S, IsMinOn (meanCost α β h p d) Set.univ S → d + d * k ≤ S := by sorry

end SupplyChainTheory
