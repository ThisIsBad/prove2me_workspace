import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem H_scaling_bounds (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∀ α : ℝ, 1 < α → M.H (α * Q) ≤ α * M.H Q) ∧
      (∀ α : ℝ, 0 < α → α < 1 → α * M.H Q ≤ M.H (α * Q)) := by sorry

end ZhengQR.Flatness
