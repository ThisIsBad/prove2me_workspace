import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem optQty_iff {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    IsOptQty (newsvendorCost μ h p) lam K Q ↔ hFun (newsvendorCost μ h p) lam K Q = optCost (newsvendorCost μ h p) lam K Q := by sorry

end ZhengQR.EOQHeuristic
