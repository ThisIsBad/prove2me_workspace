import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps

open scoped InnerProductSpace

namespace NonmonotoneLS.RLinear

/-- Which line search the run uses: the nonmonotone Wolfe conditions or the nonmonotone
Armijo conditions. The rule is fixed for the whole run. -/
inductive Rule
  | wolfe
  | armijo

variable {n : ℕ}

/-- A step accepted by the rule `r`. -/
def IsStep (r : Rule) (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α : ℝ) : Prop :=
  match r with
  | Rule.wolfe => Shared.IsWolfeStep p f x d C α
  | Rule.armijo => Shared.IsArmijoStep p f x d C α

/-- An (infinite) run of the Nonmonotone Line Search Algorithm (p. 1044) with parameters `p`
and line-search rule `r`: iterates `x`, directions `d`, steps `α` and weights `η` with
`x_{k+1} = x_k + α_k d_k`, `η_k ∈ [η_min, η_max]`, and `α_k` accepted by the rule at
`(x_k, d_k)` with reference value `C_k` of (1.6). The convergence test is not modelled. -/
structure IsNLSARun (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ) : Prop where
  update : ∀ k, x (k + 1) = x k + α k • d k
  eta_mem : ∀ k, η k ∈ Set.Icc p.ηmin p.ηmax
  step : ∀ k, IsStep r p f (x k) (d k) (Shared.costC f x η k) (α k)

/-- The direction assumption (2.4)–(2.5) with constants `c₁, c₂`, required at **every** `k`:
`∇f(x_k) d_k ≤ -c₁ ‖∇f(x_k)‖²` and `‖d_k‖ ≤ c₂ ‖∇f(x_k)‖`. -/
def DirectionBounds (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (c₁ c₂ : ℝ) : Prop :=
  ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
    ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖

end NonmonotoneLS.RLinear
