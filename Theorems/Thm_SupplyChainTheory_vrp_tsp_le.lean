import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem vrp_tsp_le {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) : tspOpt c ≤ vrpOpt c C := by sorry

end SupplyChainTheory
