import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem aFun_props {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    StrictMonoOn (aFun (newsvendorCost μ h p) lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (aFun (newsvendorCost μ h p) lam K) ∧
    (∃! Q : ℝ, IsOptQty (newsvendorCost μ h p) lam K Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty (newsvendorCost μ h p) lam K Q ↔ aFun (newsvendorCost μ h p) lam K Q = lam * K)) ∧
    (∀ K' : ℝ, K < K' → ∀ Q Q' : ℝ,
      IsOptQty (newsvendorCost μ h p) lam K Q → IsOptQty (newsvendorCost μ h p) lam K' Q' →
        Q < Q' ∧ reorderPt (newsvendorCost μ h p) lam K' Q' < reorderPt (newsvendorCost μ h p) lam K Q) := by sorry

end ZhengQR.EOQHeuristic
