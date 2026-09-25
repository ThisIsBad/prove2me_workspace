import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem two_matching_cut_form {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T)
    (hteeth : ∀ k, (T k).card = 2) :
    3 * s + 1 ≤ edgesLeaving τ H + ∑ k, edgesLeaving τ (T k) := by sorry

end SupplyChainTheory
