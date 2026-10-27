import Mathlib
import Definitions.Def_MultPacing_Existence_Limit

namespace MultPacing.Existence

theorem theorem_1_feasible {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H : ℕ → ℝ) (M : ℝ) (α : ℕ → N → ℝ) (αs : N → ℝ)
    (xs ps ss : N → G → ℝ) (hlim : IsSmoothedLimit P ε H M α αs xs ps ss) :
    (∀ j, ∑ i, xs i j ≤ 1) ∧
    (∀ j, (∃ i, 0 < P.v i j) → ∑ i, xs i j = 1) ∧
    (∀ i j, 0 < xs i j → ∀ k, αs k * P.v k j ≤ αs i * P.v i j) := by sorry

end MultPacing.Existence

