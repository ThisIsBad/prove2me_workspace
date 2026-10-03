import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 9, inequality (1.3) and the Definition following it, for a function whose
domain is the whole space `E_n`: a vector `g` is a **subgradient** of `f` at `x₀` if
`f x - f x₀ ≥ (g, x - x₀)` for every `x ∈ E_n`. -/
def IsSubgradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ g : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), f x - f x₀ ≥ inner ℝ g (x - x₀)

end ShorNonsmooth.AlmostDiff
