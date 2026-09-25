import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem vrp_radial_bound {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) :
    2 * ((n : ℝ) / C) * avgDepotDist c ≤ vrpOpt c C := by sorry

end SupplyChainTheory
