import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem H_four_needed :
    (∃ P : Fin 3 → Fin 5 → Fin 14,
      (∀ i, P i 0 = hu ∧ P i 4 = hv) ∧
      (∀ i (k : Fin 4), H.Adj (P i k.castSucc) (P i k.succ)) ∧
      (∀ i k, P i k ≠ hx ∧ P i k ≠ hy ∧ P i k ≠ hz) ∧
      (∀ i i' (k k' : Fin 5), 0 < k → k < 4 → P i k = P i' k' → i = i' ∧ k = k') ∧
      (∀ w, w ≠ hx → w ≠ hy → w ≠ hz → ∃ i k, P i k = w) ∧
      (∀ a b, a ≠ hx → a ≠ hy → a ≠ hz → b ≠ hx → b ≠ hy → b ≠ hz → H.Adj a b →
        ∃ (i : Fin 3) (k : Fin 4), s(a, b) = s(P i k.castSucc, P i k.succ))) ∧
    ∀ (S : Finset (Fin 3)) (D : Finset (Sym2 (Fin 14))), EdsRestricted S D → 4 ≤ D.card := by sorry

end EdgeDomSets.NPC

