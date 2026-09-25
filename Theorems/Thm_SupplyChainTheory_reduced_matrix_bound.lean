import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem reduced_matrix_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hn : 2 ≤ n) (ρ κ : Fin n → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ i j, i ≠ j → 0 ≤ reducedCost c ρ κ i j) :
    ∑ i, ρ i + ∑ j, κ j ≤ optTourLength c := by sorry

end SupplyChainTheory
