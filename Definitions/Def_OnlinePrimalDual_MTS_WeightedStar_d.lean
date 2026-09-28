import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar

namespace OnlinePrimalDual.MTS

/-- `d(i) := 2d′(i)` (p. 143, "From now on we only use `d(i) = 2d′(i)` to denote the cost of
moving from state `i` to any other state"), the per-state transition charge Lemma 6.1 and 6.2
use throughout. -/
def WeightedStar.d {V : Type*} (ws : WeightedStar V) (v : V) : ℝ :=
  2 * ws.centerDist v

end OnlinePrimalDual.MTS
