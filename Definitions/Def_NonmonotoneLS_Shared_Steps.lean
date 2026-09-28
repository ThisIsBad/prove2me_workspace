import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params

open scoped InnerProductSpace

namespace NonmonotoneLS.Shared

variable {n : ℕ}

/-- The nonmonotone Wolfe conditions (1.4)–(1.5) at the point `x` with direction `d`,
reference value `C` and step `α > 0`:
`f(x + α d) ≤ C + δ α ∇f(x) d` and `∇f(x + α d) d ≥ σ ∇f(x) d`. -/
def IsWolfeStep (p : Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α : ℝ) : Prop :=
  0 < α ∧
    f (x + α • d) ≤ C + p.δ * α * ⟪gradient f x, d⟫_ℝ ∧
    p.σ * ⟪gradient f x, d⟫_ℝ ≤ ⟪gradient f (x + α • d), d⟫_ℝ

/-- For a trial step `ᾱ`, the set of integer exponents `h` such that the step `ᾱ ρ^h`
satisfies (1.4) with reference value `C` and does not exceed `μ`. -/
def armijoAdmissible (p : Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C αbar : ℝ) : Set ℤ :=
  {h | f (x + (αbar * p.ρ ^ h) • d) ≤ C + p.δ * (αbar * p.ρ ^ h) * ⟪gradient f x, d⟫_ℝ ∧
        αbar * p.ρ ^ h ≤ p.μ}

/-- The nonmonotone Armijo conditions (p. 1044): `α = ᾱ ρ^h`, where `ᾱ > 0` is a trial step and
`h` is the largest integer such that (1.4) holds and `α ≤ μ`. -/
def IsArmijoStep (p : Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α : ℝ) : Prop :=
  ∃ αbar : ℝ, 0 < αbar ∧ ∃ h : ℤ, α = αbar * p.ρ ^ h ∧
    IsGreatest (armijoAdmissible p f x d C αbar) h

end NonmonotoneLS.Shared
