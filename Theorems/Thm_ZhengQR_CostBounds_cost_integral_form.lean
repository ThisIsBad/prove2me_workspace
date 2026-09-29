import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem cost_integral_form (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in reorderPt M.G M.lam M.K Q..reorderPt M.G M.lam M.K Q + Q, M.G y)
        = ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y ∧
      Cfun M.G M.lam M.K Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y) / Q := by sorry

end ZhengQR.CostBounds
