import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: for every feasible completion time `lam` the linear program
"minimize (7) subject to (5), (8), (9)" has a least costly schedule. -/
theorem exists_least_cost {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    ∀ lam ∈ feasibleDurations J, ∃ c : ℝ, IsLeast (costSet J lam) c := by sorry

end CriticalPath.CostCurve

