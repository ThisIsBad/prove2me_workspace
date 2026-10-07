import Mathlib
import Definitions.Def_TalagrandConc_QPoints_aConst

namespace TalagrandConc.QPoints

/-- (3.2.2): for `q ≥ 2` and `α > 1`, `a(q, α)` is the unique number `x > 1` with
`x + q α x^{-1/α} = 1 + q α`. -/
theorem eq_3_2_2 (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) :
    1 < aConst q α ∧
      aConst q α + (q : ℝ) * α * aConst q α ^ (-(1 / α)) = 1 + (q : ℝ) * α ∧
      ∀ x : ℝ, 1 < x → x + (q : ℝ) * α * x ^ (-(1 / α)) = 1 + (q : ℝ) * α →
        x = aConst q α := by sorry

end TalagrandConc.QPoints

