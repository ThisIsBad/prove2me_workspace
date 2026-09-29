import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem joint_convex {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))
      (fun z : ℝ × ℝ => qrCost (newsvendorCost μ h p) lam K z.1 z.2) := by sorry

end ZhengQR.EOQHeuristic
