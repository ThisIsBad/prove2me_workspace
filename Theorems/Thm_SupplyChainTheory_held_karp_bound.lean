import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem held_karp_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (lam : Fin n → ℝ) (r : Fin n) (G : SimpleGraph (Fin n)) (hG : Is1Tree r G)
    (hopt : ∀ G' : SimpleGraph (Fin n), Is1Tree r G' →
      graphWeight (revisedCost c lam) G ≤ graphWeight (revisedCost c lam) G') :
    graphWeight c G + ∑ i, lam i * ((G.degree i : ℝ) - 2) ≤ optTourLength c := by sorry

end SupplyChainTheory
