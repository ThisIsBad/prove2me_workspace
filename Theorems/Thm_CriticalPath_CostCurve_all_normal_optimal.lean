import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: the all-normal solution `y = D`, with every job started as
early as possible (`t = t⁽⁰⁾(D)`), is a minimum cost schedule for `λ = tₙ⁽⁰⁾(D)`. -/
theorem all_normal_optimal {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    IsOptimalSchedule J (earliest N J.D (Fin.last n)) J.D (earliest N J.D) := by sorry

end CriticalPath.CostCurve

