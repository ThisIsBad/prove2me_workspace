import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

theorem theorem_2 {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] (P : PacingGame N G)
    (ε H M : ℝ) (hε : 0 < ε) (hM : ∀ i, ∑ j, P.v i j + 2 * ε ≤ M) (hH : M / ε < H) :
    ∃ α : N → ℝ, IsSmoothedPNE P ε H α := by sorry

end MultPacing.Existence

