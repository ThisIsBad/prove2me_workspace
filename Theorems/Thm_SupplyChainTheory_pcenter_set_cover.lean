import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem pcenter_set_cover {n m : ℕ} (c : Fin n → Fin m → ℝ) (p : ℕ) (hp : 1 ≤ p) (hpm : p ≤ m)
    (r : ℝ) (hr : 0 ≤ r) :
    pCenterValue c p ≤ r ↔ ∃ S : Finset (Fin m), S.card ≤ p ∧ ∀ i, ∃ j ∈ S, c i j ≤ r := by sorry

end SupplyChainTheory
