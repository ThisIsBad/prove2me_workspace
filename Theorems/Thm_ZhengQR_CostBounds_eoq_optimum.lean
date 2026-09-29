import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem eoq_optimum (M : QRModel) :
    (∀ Q : ℝ, 0 ≤ Q → Hfun M.Gd M.lam M.K Q = M.h * M.p / (M.h + M.p) * Q) ∧
    (∀ Q : ℝ, IsOptQty M.Gd M.lam M.K Q ↔ Q = M.Qd) ∧
    Cfun M.Gd M.lam M.K M.Qd = Hfun M.Gd M.lam M.K M.Qd := by sorry

end ZhengQR.CostBounds
