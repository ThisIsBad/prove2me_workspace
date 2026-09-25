import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem mst_lower_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) : graphWeight c T ≤ optTourLength c := by sorry

end SupplyChainTheory
