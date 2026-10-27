import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_budget {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    ∀ i, ∑ j, ss i j ≤ P.B i := by sorry

end MultPacing.Existence

