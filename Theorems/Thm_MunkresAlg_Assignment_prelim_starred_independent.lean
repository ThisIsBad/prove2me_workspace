import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Preliminaries, p. 33: the zeros starred by the Preliminaries are independent (and are
zeros of the reduced matrix), whatever order the zeros are considered in. -/
theorem prelim_starred_independent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : IsStart A s) :
    IsIndepZeros s.A s.starred := by sorry

end MunkresAlg.Assignment

