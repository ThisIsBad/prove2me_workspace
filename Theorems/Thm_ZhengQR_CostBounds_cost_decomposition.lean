import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem cost_decomposition (M : QRModel) :
    (∀ Q : ℝ, 0 < Q →
      Cfun M.G M.lam M.K Q = M.G (idealPt M.G) + C0fun M.G M.lam M.K Q) ∧
    (∀ Qs : ℝ, IsOptQty M.G M.lam M.K Qs →
      H0fun M.G M.lam M.K Qs = C0fun M.G M.lam M.K Qs) := by sorry

end ZhengQR.CostBounds
