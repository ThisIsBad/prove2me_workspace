import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 4.2, p. 16: `F_ε` is the set of arcs of `E` whose flow is the same
in every `ε`-optimal circulation. -/
noncomputable def fixedArcs (N : CircNetwork V) (ε : ℝ) : Finset (V × V) := by
  classical
  exact N.E.filter (fun a => IsEpsFixed N ε a.1 a.2)

end CostScaling.StrongPoly
