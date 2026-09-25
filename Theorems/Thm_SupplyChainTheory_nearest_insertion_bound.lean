import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem nearest_insertion_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (L : ℕ → List (Fin n)) (hL : IsNearestInsertionRun c L) :
    cycleLength c (L (n - 1)) ≤ 2 * optTourLength c := by sorry

end SupplyChainTheory
