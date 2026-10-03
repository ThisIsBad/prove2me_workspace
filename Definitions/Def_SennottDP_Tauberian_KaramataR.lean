import Mathlib

namespace SennottDP.Tauberian

/-- Sennott (1999), §A.4, pp. 280–281, Fig. A.1: the function `r` with a jump at `e^{-1}`:
`r(α) = 0` for `α < e^{-1}` and `r(α) = 1/α` for `α ≥ e^{-1}` (the book uses it on `(0, 1)`).
The value at the jump is `r(e^{-1}) = e`, as in Fig. A.1 and in (A.40), where
`α^n ≥ e^{-1}` is the condition for `r(α^n) = α^{-n}`. -/
noncomputable def r (x : ℝ) : ℝ :=
  if Real.exp (-1) ≤ x then x⁻¹ else 0

end SennottDP.Tauberian
