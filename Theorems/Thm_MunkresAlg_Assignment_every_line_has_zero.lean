import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, p. 36: after the Preliminaries each row and each column of the matrix contains at least
one zero, and this never changes. -/
theorem every_line_has_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) :
    (∀ i, ∃ j, s.A i j = 0) ∧ (∀ j, ∃ i, s.A i j = 0) := by sorry

end MunkresAlg.Assignment

