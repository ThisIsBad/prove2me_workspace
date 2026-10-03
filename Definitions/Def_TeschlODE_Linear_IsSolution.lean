import Mathlib

namespace TeschlODE.Linear

/-- Teschl (3.79), p. 81: `x` solves the linear first-order system `ẋ(t) = A(t) x(t)` on the
interval `I`, i.e. at every `t ∈ I` it has derivative (within `I`, so one-sided at an endpoint
that belongs to `I`) equal to `A(t) x(t)`. Only the values of `x` on `I` matter. -/
def IsSolution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ t ∈ I, HasDerivWithinAt x (Matrix.mulVec (A t) (x t)) I t

end TeschlODE.Linear
