import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.Shared

/-- The **polar** of a set `C ⊆ ℝⁿ` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §2, p. 3):
`C° = {y ∈ ℝⁿ : ⟨x, y⟩ ≤ 1 for all x ∈ C}`, with `⟨·,·⟩` the Euclidean inner product of
`EuclideanSpace ℝ (Fin n)`.

This is the one-sided polar; it is not Mathlib's `LinearMap.polar` / `StrongDual.polar`, which
use the absolute value `‖⟨x, y⟩‖ ≤ 1`. -/
def polar {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ C, ⟪x, y⟫_ℝ ≤ 1}

end ConeLifts.Shared
