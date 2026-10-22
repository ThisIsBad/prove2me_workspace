import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 5 (ii) (p. 59), under the choice (7). If `(d_y, d_x, d_τ, d_θ, d_s, d_κ)` lies in the
null space `Q` of the constraint matrix of (HLP) after adding surplus variables `s` and `κ`, then
`(d_x)ᵀd_s + d_τ d_κ = 0`. -/
theorem theorem_5_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : HLPPoint m n) (hd : InQ7 A b c d) :
    d.x ⬝ᵥ d.s + d.τ * d.κ = 0 := by sorry

end SelfDualLP.Complexity

