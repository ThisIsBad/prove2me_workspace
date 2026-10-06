import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem window_contiguous_smallest (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    (Finset.Icc 1 Q).image (y G y₁) = Finset.Icc (L G y₁ Q) (R G y₁ Q) ∧
    R G y₁ Q - L G y₁ Q + 1 = (Q : ℤ) ∧
    (∀ i ∈ Finset.Icc 1 Q, ∀ t : ℤ, t ∉ Finset.Icc (L G y₁ Q) (R G y₁ Q) → G (y G y₁ i) ≤ G t) ∧
    (∀ T : Finset ℤ, T.card = Q → ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i) ≤ ∑ t ∈ T, G t) := by sorry

end FedergruenZhengRQ.OPT

