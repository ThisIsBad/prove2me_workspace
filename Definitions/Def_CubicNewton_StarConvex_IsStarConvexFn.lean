import Mathlib

namespace CubicNewton.StarConvex

/-- Star-convex function (Nesterov–Polyak 2006, Section 4.1, p. 188, Definition 1, (4.1)).
`f` is star-convex relative to `F` if its set `X*` of global minimizers over the whole space is
nonempty, and for every global minimizer `x*`, every `x ∈ F` and every `α ∈ [0, 1]`,
`f(α x* + (1 − α) x) ≤ α f(x*) + (1 − α) f(x)`.
The point `x` ranges over `F`, as in the display (4.1). This is a property of a function, not
Mathlib's `StarConvex` (a property of sets). -/
def IsStarConvexFn {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∃ xs : EuclideanSpace ℝ (Fin n), ∀ y, f xs ≤ f y) ∧
    ∀ xs : EuclideanSpace ℝ (Fin n), (∀ y, f xs ≤ f y) →
      ∀ x ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1,
        f (α • xs + (1 - α) • x) ≤ α * f xs + (1 - α) * f x

end CubicNewton.StarConvex
