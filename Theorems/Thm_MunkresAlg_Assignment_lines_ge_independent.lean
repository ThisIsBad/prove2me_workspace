import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic

namespace MunkresAlg.Assignment

/-- §1, Step 3, first bracket, p. 34: any set of lines containing all the zeros of a matrix has
at least as many lines as the maximal number of independent zeros. -/
theorem lines_ge_independent {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n))
    (hcov : CoversZeros B R C) :
    maxIndepZeros B ≤ R.card + C.card := by sorry

end MunkresAlg.Assignment

