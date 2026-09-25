import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem hakimi {n p : ℕ} (d : Fin n → Fin n → ℝ) (hw : Fin n → ℝ) (hwn : ∀ i, 0 ≤ hw i)
    (hp : 1 ≤ p) (hpn : p ≤ n)
    (htri : ∀ i j k : Fin n, d i k ≤ d i j + d j k)
    (X : Fin p → NetPoint n)
    (hedge : ∀ k, d (X k).u (X k).w ≤ (X k).len ∧ d (X k).w (X k).u ≤ (X k).len) :
    ∃ S : Finset (Fin n), S.card = p ∧
      ∑ i, hw i * nearestNodeDist d i S ≤ ∑ i, hw i * nearestDist d i X := by sorry

end SupplyChainTheory
