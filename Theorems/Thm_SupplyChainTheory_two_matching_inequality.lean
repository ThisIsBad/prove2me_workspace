import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem two_matching_inequality {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T)
    (hteeth : ∀ k, (T k).card = 2) :
    edgesWithin τ H + ∑ k, edgesWithin τ (T k) ≤ H.card + (s - 1) / 2 := by sorry

end SupplyChainTheory
