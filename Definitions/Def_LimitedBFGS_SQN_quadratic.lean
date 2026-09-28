import Mathlib

open Matrix

namespace LimitedBFGS.SQN

/-- The gradient `g(x) = A x + b` of the quadratic `f(x) = ½ xᵀAx + bᵀx`
(Nocedal 1980, p. 775, Property (b)). -/
def grad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  A *ᵥ x + b

/-- The exact line-search step along `d` from `x` for `f(x) = ½ xᵀAx + bᵀx`:
`α = −(g(x)ᵀd) / (dᵀAd)`. For `A` positive definite and `d ≠ 0` this is the unique minimizer
of `α ↦ f(x + α d)` (Nocedal 1980, p. 777, "exact line searches"). For `d = 0` Lean's
`0 / 0 = 0` gives `α = 0`, and the iterate does not move. -/
noncomputable def exactStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (x d : Fin n → ℝ) : ℝ :=
  -(grad A b x ⬝ᵥ d) / (d ⬝ᵥ (A *ᵥ d))

end LimitedBFGS.SQN
