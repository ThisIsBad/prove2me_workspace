import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease

/-- The error function (4:5) of an estimate `x` of the solution `h` of `Ax = k`:
`f(x) = (h − x, A(h − x))`. -/
def errorFun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h x : Fin n → ℝ) : ℝ :=
  (h - x) ⬝ᵥ (A *ᵥ (h - x))

end ConjGrad.ErrorDecrease
