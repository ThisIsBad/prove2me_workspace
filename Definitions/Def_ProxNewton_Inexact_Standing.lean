import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- `x⋆` is an optimal solution of problem (1.1): it lies in the domain `D` of `h` and minimizes
`f = g + h` over `D` (hence over the whole space, `f = +∞` off `D`). -/
def IsMinimizer (g : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n)) : Prop :=
  xstar ∈ D ∧ ∀ y ∈ D, g xstar + h xstar ≤ g y + h y

/-- The standing assumptions (i)–(ii) of §3.4 on the smooth part `g`: `g` is twice continuously
differentiable and strongly convex with constant `m > 0` in the sense of Definition 3.2, and `∇g`
and `∇²g` are Lipschitz continuous with constants `L1` and `L2`. -/
structure SmoothPartAssumptions (g : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 g
  m_pos : 0 < m
  strongConvex : ∀ x y, g x + ⟪gradient g x, y - x⟫ + m / 2 * ‖x - y‖ ^ 2 ≤ g y
  L1_nonneg : 0 ≤ L1
  grad_lipschitz : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖
  L2_nonneg : 0 ≤ L2
  hessian_lipschitz : ∀ x y, ‖hessian g x - hessian g y‖ ≤ L2 * ‖x - y‖

/-- `∇²g(x) ⪯ M I` for every `x`: `vᵀ ∇²g(x) v ≤ M ‖v‖²`. -/
def HessianLE (g : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) : Prop :=
  ∀ x v, ⟪hessian g x v, v⟫ ≤ M * ‖v‖ ^ 2

end ProxNewton.Inexact
