import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem hFun_props {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    StrictMonoOn (hFun (newsvendorCost μ h p) lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (hFun (newsvendorCost μ h p) lam K) ∧
    ContinuousWithinAt (hFun (newsvendorCost μ h p) lam K) (Set.Ici 0) 0 ∧
    (∀ Q Q' : ℝ, 0 ≤ Q → Q < Q' → hFun (newsvendorCost μ h p) lam K Q' - hFun (newsvendorCost μ h p) lam K Q ≤ h * p / (h + p) * (Q' - Q)) ∧
    Tendsto (fun Q : ℝ => hFun (newsvendorCost μ h p) lam K Q / Q) atTop (𝓝 (h * p / (h + p))) := by sorry

end ZhengQR.EOQHeuristic
