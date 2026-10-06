import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem lemma2_optimal_order_size (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (hco : Coercive G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    (∃ q : ℕ, 1 ≤ q ∧ Cstar κ G y₁ q ≤ G (y G y₁ (q + 1))) ∧
    ∀ q : ℕ, 1 ≤ q → Cstar κ G y₁ q ≤ G (y G y₁ (q + 1)) →
      (∀ q' : ℕ, 1 ≤ q' → q' < q → G (y G y₁ (q' + 1)) < Cstar κ G y₁ q') →
      ∀ Q : ℕ, 1 ≤ Q → Cstar κ G y₁ q ≤ Cstar κ G y₁ Q := by sorry

end FedergruenZhengRQ.OPT

