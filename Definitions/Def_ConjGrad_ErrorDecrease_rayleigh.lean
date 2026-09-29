import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease

/-- The Rayleigh quotient (4:12) of a vector `z` with respect to the matrix `A`:
`μ(z) = (z, Az) / |z|²`. Lean's convention `t / 0 = 0` gives `μ(0) = 0`. -/
noncomputable def rayleigh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : ℝ :=
  (z ⬝ᵥ (A *ᵥ z)) / (z ⬝ᵥ z)

end ConjGrad.ErrorDecrease
