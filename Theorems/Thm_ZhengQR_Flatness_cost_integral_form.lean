import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem cost_integral_form (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in M.r Q..M.r Q + Q, M.G y) = (∫ y in (0 : ℝ)..Q, M.H y) ∧
      M.C Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, M.H y) / Q := by sorry

end ZhengQR.Flatness
