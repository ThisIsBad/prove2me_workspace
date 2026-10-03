import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, Theorem 1.15, in the form its proof establishes: a convex function `f`
on `E_n` is almost differentiable, and at every point `x₀` every almost-gradient of `f` is a
subgradient of `f` at `x₀`.

The printed statement says the almost-gradients "coincide with" the subgradients; that set
equality is false (for `f(x) = |x|` on `ℝ¹` the almost-gradients at `0` are `{-1, 1}` while the
subgradients form `[-1, 1]`), and the book's proof shows only the inclusion stated here. -/
theorem convex_almostDifferentiable_almostGradient_isSubgradient {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    AlmostDifferentiable f ∧
      ∀ x₀ : EuclideanSpace ℝ (Fin n), ∀ g ∈ almostGradients f x₀,
        IsSubgradient f x₀ g := by sorry

end ShorNonsmooth.AlmostDiff

