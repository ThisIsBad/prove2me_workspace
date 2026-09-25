import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem vcg_core_characterization {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ)
    (hV : IsCoalitionalValue V) :
    (BidderSubmodular V ↔ ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → ∀ π,
        InCore V S π ↔ (∑ k ∈ S, π k = V S ∧ ∀ k ∈ S, k ≠ 0 → 0 ≤ π k ∧ π k ≤ vcgPayoff V S k))
      ∧ (BidderSubmodular V ↔ ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S →
          InCore V S (vcgPayoff V S)) := by sorry

end SupplyChainTheory
