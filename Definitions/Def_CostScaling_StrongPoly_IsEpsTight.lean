import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 2.2, p. 7: a circulation is `ε`-tight when it is `ε`-optimal but is
not `ε'`-optimal for any smaller error parameter `ε'`. This includes attainment
at `ε`, rather than just equality with the infimum `epsOpt`. -/
def IsEpsTight (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) : Prop :=
  IsEpsOptimal N f ε ∧ ∀ ε' : ℝ, ε' < ε → ¬ IsEpsOptimal N f ε'

end CostScaling.StrongPoly
