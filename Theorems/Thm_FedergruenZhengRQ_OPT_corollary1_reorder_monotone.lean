import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem corollary1_reorder_monotone (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1) ∧
    (L G y₁ Q - 1) - 1 ≤ L G y₁ (Q + 1) - 1 ∧ L G y₁ (Q + 1) - 1 ≤ L G y₁ Q - 1 ∧
    (∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q) ∧
    (∀ r : ℤ, cost κ G (L G y₁ (Q + 1) - 1) (Q + 1) ≤ cost κ G r (Q + 1)) := by sorry

end FedergruenZhengRQ.OPT

