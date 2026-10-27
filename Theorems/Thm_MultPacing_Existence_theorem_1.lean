import Mathlib
import Definitions.Def_MultPacing_Existence_Model

namespace MultPacing.Existence

theorem theorem_1 {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] (P : PacingGame N G) :
    ∃ (α : N → ℝ) (x : N → G → ℝ) (p : G → ℝ), IsSPPE P α x p := by sorry

end MultPacing.Existence

