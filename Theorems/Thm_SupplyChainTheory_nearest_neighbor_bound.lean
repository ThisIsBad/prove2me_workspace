import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem nearest_neighbor_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (τ : Equiv.Perm (Fin n)) (hτ : IsNearestNeighborTour c τ) :
    tourLength c τ ≤ (1 / 2 : ℝ) * (Nat.clog 2 n + 1) * optTourLength c := by sorry

end SupplyChainTheory
