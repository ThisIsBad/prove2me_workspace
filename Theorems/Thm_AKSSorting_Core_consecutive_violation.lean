import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain
import Definitions.Def_AKSSorting_Core_Rbeta

namespace AKSSorting.Core

/-- Lemma 12(a) (Ajtai–Komlós–Szemerédi 1983, p. 14). Let `C` be a chain on level `i`, `G` a
position (an injective assignment of contents to registers), `β > 0`, and `t₁ < t₂` nodes of
`Dom(C)` with `¬R^β_G(t₁, t₂)`. Then there are consecutive nodes `t₁' < t₂'` (`t₂' = t₁' + 1`)
with `t₁ ≤ t₁' < t₂' ≤ t₂` and `¬R^β_G(t₁', t₂')`. -/
theorem consecutive_violation {R : Type} [DecidableEq R] {α : Type} [LinearOrder α] {i : ℕ}
    (C : Fin (2 ^ i) → Finset R) (hC : IsChain C) (G : R → α) (hG : Function.Injective G)
    (β : ℝ) (hβ : 0 < β) (t₁ t₂ : Fin (2 ^ i)) (h12 : t₁ < t₂) (hR : ¬ Rbeta G C β t₁ t₂) :
    ∃ t₁' t₂' : Fin (2 ^ i), t₁'.val + 1 = t₂'.val ∧ t₁ ≤ t₁' ∧ t₂' ≤ t₂ ∧
      ¬ Rbeta G C β t₁' t₂' := by sorry

end AKSSorting.Core
