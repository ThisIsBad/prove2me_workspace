import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Lemma 2 of Anderson and Potts (2004), p. 690: `π_E` is an optimal schedule for the
extended problem (E), among all feasible nonpreemptive schedules of (E). -/
theorem piE_optimal {n : ℕ} (I : Instance n) :
    IsOptimal (rE I) (pE I) (wE I) (piE I) := by sorry

end DelayedSWPT.Extended

