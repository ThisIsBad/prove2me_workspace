import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem vrp_tsp_bounds {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) :
    max (2 * ((n : ℝ) / C) * avgDepotDist c) (tspOpt c) ≤ vrpOpt c C
      ∧ vrpOpt c C ≤ 2 * ⌈(n : ℝ) / C⌉₊ * avgDepotDist c + (1 - 1 / (C : ℝ)) * tspOpt c := by sorry

end SupplyChainTheory
