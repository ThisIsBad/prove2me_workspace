import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem hFun_sandwich {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 ≤ Q) :
    h0Fun (newsvendorCost μ h p) lam K Q ≤ hFun (eoqCost lam L h p) lam K Q ∧
    hFun (eoqCost lam L h p) lam K Q ≤ hFun (newsvendorCost μ h p) lam K Q ∧
    aFun (newsvendorCost μ h p) lam K Q ≤ aFun (eoqCost lam L h p) lam K Q := by sorry

end ZhengQR.EOQHeuristic
