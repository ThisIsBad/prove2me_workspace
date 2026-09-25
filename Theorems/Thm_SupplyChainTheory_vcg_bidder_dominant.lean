import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem vcg_bidder_dominant {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (hV : IsCoalitionalValue V) :
    (InCore V Finset.univ (vcgPayoff V Finset.univ) → BidderDominant V Finset.univ (vcgPayoff V Finset.univ))
      ∧ (¬ InCore V Finset.univ (vcgPayoff V Finset.univ) →
          (¬ ∃ π, BidderDominant V Finset.univ π)
          ∧ ∀ π, InCore V Finset.univ π → vcgPayoff V Finset.univ 0 < π 0) := by sorry

end SupplyChainTheory
