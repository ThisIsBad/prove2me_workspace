import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule
import Definitions.Def_CriticalPath_CostCurve_IsPiecewiseLinearOn

namespace CriticalPath.CostCurve

/-- Kelley–Walker (1959), §3, p. 165: the project cost curve `C(lam)`, the minimum of (7)
subject to (5), (8), (9), is on the set `Λ` of feasible completion times a non-increasing,
piecewise linear (finitely many affine pieces covering `Λ`), convex function. -/
theorem project_cost_curve {n : ℕ} (N : ProjectNetwork n) (J : JobData N) (C : ℝ → ℝ)
    (hC : ∀ lam ∈ feasibleDurations J, IsLeast (costSet J lam) (C lam)) :
    AntitoneOn C (feasibleDurations J) ∧
      IsPiecewiseLinearOn C (feasibleDurations J) ∧
      ConvexOn ℝ (feasibleDurations J) C := by sorry

end CriticalPath.CostCurve

