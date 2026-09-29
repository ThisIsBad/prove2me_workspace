import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem eoqQty_le_optQty {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    eoqQty lam K h p ≤ Qs := by sorry

end ZhengQR.EOQHeuristic
