import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d

namespace OnlinePrimalDual.MTS

/-- The cost, in the **new** MTS model, of a solution described by the `k` phases it visits:
`s i` is the state visited during phase `i`, and each phase costs exactly `d(s i)` regardless of
how much service was actually performed during it (p. 144-145, "If the algorithm is in state `i`
during phase `p` then it pays a cost `d(i)`. The algorithm pays the full cost of the phase even
if it was in state `i` only during part of the phase"). -/
def costNewPhases {V : Type*} {k : ℕ} (ws : WeightedStar V) (s : Fin k → V) : ℝ :=
  ∑ i, ws.d (s i)

end OnlinePrimalDual.MTS
