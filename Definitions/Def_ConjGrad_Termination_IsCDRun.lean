import Mathlib

open Matrix

namespace ConjGrad.Termination

/-- A run of the method of conjugate directions (cd-method) of Hestenes–Stiefel 1952, §4,
p. 412, for the system `Ax = k`: sequences of estimates `x i`, residuals `r i` and directions
`p i` (indices 0-based) such that
* every residual is the residual of its estimate, `rᵢ = k − Axᵢ` (the initial step and the
  paper's "the residual rᵢ = k − Axᵢ"; (4:1c) follows);
* the estimate is updated by (4:1a)–(4:1b): `xᵢ₊₁ = xᵢ + aᵢpᵢ` with `aᵢ = (pᵢ,rᵢ)/(pᵢ,Apᵢ)`;
* each new direction is conjugate to all previous ones, (4:2): `(pᵢ₊₁, Apⱼ) = 0` for
  `j = 0, …, i`.
The initial direction `p₀` is arbitrary, as in the paper. -/
structure IsCDRun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n → ℝ)
    (x r p : ℕ → Fin n → ℝ) : Prop where
  /-- `rᵢ = k − Axᵢ` -/
  residual : ∀ i, r i = k - A *ᵥ x i
  /-- (4:1a), (4:1b) -/
  step : ∀ i, x (i + 1) = x i + ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) • p i
  /-- (4:2) -/
  conj : ∀ i, ∀ j ≤ i, p (i + 1) ⬝ᵥ (A *ᵥ p j) = 0

end ConjGrad.Termination
