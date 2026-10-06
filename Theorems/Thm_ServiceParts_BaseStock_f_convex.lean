import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 19: "Recall that fₙ(y) is a convex function." For every horizon n ≥ 1. -/
theorem f_convex (M : Model) (n : ℕ) (hn : 1 ≤ n) : ConvexOn ℝ univ (M.f n) := by sorry

end ServiceParts.BaseStock

