import Mathlib
import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem risk_diversification (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (N : ℕ) (hN : 0 < N) (S : ℝ) :
    (IsMinOn (meanCost α β h p d) Set.univ S → IsMinOn (meanCost α β h p (N * d)) Set.univ (N * S))
      ∧ meanCost α β h p (N * d) (N * S) = N * meanCost α β h p d S
      ∧ varCost α β h p (N * d) (N * S) = (N : ℝ) ^ 2 * varCost α β h p d S := by sorry

end SupplyChainTheory
