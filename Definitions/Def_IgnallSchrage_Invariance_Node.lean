import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Invariance

/-- The change of location and scale of the Appendix (p. 411): from processing times `x'` of
problem `P'`, the processing times `x̃_i = H (x'_i + G)` of problem `P̃` (first add `G`, then
multiply by `H`). -/
def shiftScale {n : ℕ} (H G : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => H * (x i + G)

end IgnallSchrage.Invariance
