import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem cost_flatter_than_eoq (M : QRModel) (Qs : ℝ) (hQs : M.IsOptQty Qs)
    (α : ℝ) (hα : 0 < α) :
    M.C (α * Qs) / M.C Qs ≤ 1 / 2 * (α + 1 / α) := by sorry

end ZhengQR.Flatness

