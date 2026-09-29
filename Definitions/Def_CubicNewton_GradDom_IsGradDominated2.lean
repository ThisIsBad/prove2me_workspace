import Mathlib

namespace CubicNewton.GradDom

/-- Gradient domination of degree `p = 2` (Nesterov–Polyak 2006, Section 4.2, p. 191,
Definition 3 with `p = 2`): `f` attains its global minimum over `F` at `xs ∈ F`, the constant
`τ` (the paper's `τ_f`) is positive, and for every `x ∈ F`
`f(x) − f(x*) ≤ τ_f ‖f′(x)‖²`  (4.7),
with `g x` in the role of `f′(x)`. -/
def IsGradDominated2 {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  xs ∈ F ∧ (∀ y ∈ F, f xs ≤ f y) ∧ 0 < τ ∧ ∀ x ∈ F, f x - f xs ≤ τ * ‖g x‖ ^ 2

end CubicNewton.GradDom
