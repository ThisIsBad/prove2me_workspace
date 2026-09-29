import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

namespace KontsevichHMS

open Brane

/-- Kontsevich's computation on the two-torus: the triangles contributing to a structure
constant of `m₂` are labelled by an arithmetic progression whose terms have squares
proportional to their areas, so each structure constant is a value of a classical
theta-function (or vanishes, when no triangle contributes). -/
theorem mTwoCoeff_theta (area : ℝ) (harea : 0 < area) (b₁ b₂ b₃ : Brane)
    (h₁₂ : Transverse b₁ b₂) (h₂₃ : Transverse b₂ b₃) (h₁₃ : Transverse b₁ b₃)
    (hc₁ : b₁.conn = 0) (hc₂ : b₂.conn = 0) (hc₃ : b₃.conn = 0)
    (p q r : Torus) (hp : p ∈ isect b₁ b₂) (hq : q ∈ isect b₂ b₃) (hr : r ∈ isect b₁ b₃) :
    mTwoCoeff area b₁ b₂ b₃ p q r = 0 ∨
      ∃ a b : ℝ, a ≠ 0 ∧
        mTwoCoeff area b₁ b₂ b₃ p q r
          = ∑' n : ℤ, Complex.exp (-((a * (n : ℝ) + b) ^ 2 : ℝ)) := by sorry

end KontsevichHMS
