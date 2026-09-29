import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem reorder_opt_iff {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    (∃ r : ℝ, IsOptReorder (newsvendorCost μ h p) lam K Q r) ∧
      ∀ r : ℝ, IsOptReorder (newsvendorCost μ h p) lam K Q r ↔ newsvendorCost μ h p r = newsvendorCost μ h p (r + Q) := by sorry

end ZhengQR.EOQHeuristic
