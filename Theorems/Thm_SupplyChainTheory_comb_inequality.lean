import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem comb_inequality {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T) :
    edgesWithin τ H + ∑ k, edgesWithin τ (T k) + (s + 1) / 2
      ≤ H.card + ∑ k, ((T k).card - 1) := by sorry

end SupplyChainTheory
