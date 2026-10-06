import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

namespace FedergruenZhengRQ.OPT

theorem algorithmOPT_optimal (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ) (hG : NegUnimodal G)
    (hco : Coercive G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ r : ℤ, ∃ Q : ℕ, optRun κ G y₁ n = some (r, Q) ∧ 1 ≤ Q ∧
      ∀ r' : ℤ, ∀ Q' : ℕ, 1 ≤ Q' → cost κ G r Q ≤ cost κ G r' Q' := by sorry

end FedergruenZhengRQ.OPT

