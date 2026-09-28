import Mathlib

namespace GallegoOzerADI.PositiveSetup

/-- Definition 1 (Gallego–Özer 2001, p. 1349): for `a ≥ 0`, `b ≥ 0`, a function `g : ℝ → ℝ` is
`(a, b)`-convex, `g ∈ C(a, b)`, if
`g (θ x₁ + (1 - θ) x₂) ≤ θ (a + g x₁) + (1 - θ) (b + g x₂)` for all `x₁ ≤ x₂` and `θ ∈ [0, 1]`.
The inequality is required only for ordered pairs `x₁ ≤ x₂`; `(0, K)`-convexity is Scarf's
`K`-convexity. The nonnegativity of `a` and `b` is the paper's standing requirement on the
parameters and is carried as a hypothesis by every theorem that uses this class. -/
def ABConvex (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    g (θ * x₁ + (1 - θ) * x₂) ≤ θ * (a + g x₁) + (1 - θ) * (b + g x₂)

end GallegoOzerADI.PositiveSetup
