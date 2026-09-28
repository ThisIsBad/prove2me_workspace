import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: the reduction of the project completion time stops at the
all-crash earliest completion time. The linear program (5), (8), (9) has a schedule for `lam`
exactly when `lam ≥ tₙ⁽⁰⁾(d)`. -/
theorem feasibleDurations_eq_Ici {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    feasibleDurations J = Set.Ici (earliest N J.d (Fin.last n)) := by sorry

end CriticalPath.CostCurve

