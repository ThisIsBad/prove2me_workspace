import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem integral_H_le (M : QRModel) (α Q : ℝ) (hα : 0 < α) (hQ : 0 < Q) :
    (∫ y in Q..α * Q, M.H y) ≤ (α ^ 2 - 1) / 2 * Q * M.H Q := by sorry

end ZhengQR.Flatness
