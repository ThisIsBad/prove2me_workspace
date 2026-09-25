import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem christofides_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) (M : Finset (Sym2 (Fin n)))
    (hM : IsMinMatchingOn c (oddNodes T) M) (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v)
    (hW : (W.edges : Multiset (Sym2 (Fin n))) = T.edgeFinset.val + M.val)
    (τ : Equiv.Perm (Fin n)) (hτ : IsShortcut W.support τ) :
    tourLength c τ ≤ (3 / 2 : ℝ) * optTourLength c := by sorry

end SupplyChainTheory
