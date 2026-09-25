import Definitions.Def_SupplyChainTheory_vrp

namespace SupplyChainTheory

theorem iotp_bound {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) (L : List (Fin (n + 1))) (hL : IsCustomerTour L) :
    ∃ R, IsVRPSolution C R ∧ solutionCost c R
      ≤ 2 * ⌈(n : ℝ) / C⌉₊ * avgDepotDist c + (1 - (⌈(n : ℝ) / C⌉₊ : ℝ) / n) * routeCost c L := by sorry

end SupplyChainTheory
