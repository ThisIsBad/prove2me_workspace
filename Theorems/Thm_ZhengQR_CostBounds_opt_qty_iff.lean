import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem opt_qty_iff (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    IsOptQty M.G M.lam M.K Q ↔ Hfun M.G M.lam M.K Q = Cfun M.G M.lam M.K Q := by sorry

end ZhengQR.CostBounds
