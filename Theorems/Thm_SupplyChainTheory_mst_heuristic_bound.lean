import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem mst_heuristic_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) (v : Fin n) (W : T.Walk v v)
    (hW : ∀ e ∈ T.edgeSet, W.edges.count e = 2) (τ : Equiv.Perm (Fin n))
    (hτ : IsShortcut W.support τ) :
    tourLength c τ ≤ 2 * optTourLength c := by sorry

end SupplyChainTheory
