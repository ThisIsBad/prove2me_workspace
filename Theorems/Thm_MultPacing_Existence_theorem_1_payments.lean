import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_payments {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    (∀ i j, ps i j = highestOther P.v αs i j) ∧ (∀ i j, ss i j = xs i j * ps i j) := by sorry

end MultPacing.Existence

