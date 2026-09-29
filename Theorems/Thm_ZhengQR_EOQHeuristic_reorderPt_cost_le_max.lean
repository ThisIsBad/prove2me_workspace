import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem reorderPt_cost_le_max {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ∀ Q : ℝ, 0 < Q → ∀ r : ℝ,
      newsvendorCost μ h p (reorderPt (newsvendorCost μ h p) lam K Q) ≤ max (newsvendorCost μ h p r) (newsvendorCost μ h p (r + Q)) := by sorry

end ZhengQR.EOQHeuristic
