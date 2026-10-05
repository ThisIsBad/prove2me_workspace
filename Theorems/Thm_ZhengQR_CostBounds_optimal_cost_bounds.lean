import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem optimal_cost_bounds (M : QRModel) (Qs : ℝ) (hQs : IsOptQty M.G M.lam M.K Qs) :
    C0fun M.G M.lam M.K Qs ≤ M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd ∧
    Cfun M.Gd M.lam M.K M.Qd ≤ Cfun M.G M.lam M.K Qs ∧
    Cfun M.G M.lam M.K Qs ≤ M.G (idealPt M.G) + M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd := by sorry

end ZhengQR.CostBounds

