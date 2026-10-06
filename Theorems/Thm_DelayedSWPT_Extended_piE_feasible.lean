import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Anderson and Potts (2004), §3.2, p. 690: the schedule `π_E` is feasible for the extended
problem (E). -/
theorem piE_feasible {n : ℕ} (I : Instance n) : IsFeasible (rE I) (pE I) (piE I) := by sorry

end DelayedSWPT.Extended

