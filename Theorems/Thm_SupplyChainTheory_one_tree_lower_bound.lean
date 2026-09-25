import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem one_tree_lower_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (r : Fin n) : opt1TreeLength c r ≤ optTourLength c := by sorry

end SupplyChainTheory
