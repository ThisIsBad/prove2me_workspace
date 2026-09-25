import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem vcg_core_lemma {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (hV : IsCoalitionalValue V) :
    (∃ π, InCore V Finset.univ π)
      ∧ ∀ k : Fin (n + 1), k ≠ 0 →
        IsGreatest {x | ∃ π, InCore V Finset.univ π ∧ x = π k} (vcgPayoff V Finset.univ k) := by sorry

end SupplyChainTheory
