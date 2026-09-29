import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem eoq_H_linear (M : QRModel) (Q : ℝ) (hQ : 0 ≤ Q) :
    (0 < Q → M.rd Q = M.lam * M.L - M.h / (M.h + M.p) * Q) ∧
      M.Hd Q = M.h * M.p / (M.h + M.p) * Q := by sorry

end ZhengQR.Flatness
