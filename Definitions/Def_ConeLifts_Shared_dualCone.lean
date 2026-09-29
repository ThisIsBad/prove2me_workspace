import Mathlib

open scoped InnerProductSpace

namespace ConeLifts.Shared

/-- The **dual cone** of `K ⊆ ℝᵐ` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §2, p. 3):
`K* = {y ∈ ℝᵐ : ⟨x, y⟩ ≥ 0 for all x ∈ K}`, with `⟨·,·⟩` the Euclidean inner product of
`EuclideanSpace ℝ (Fin m)`. -/
def dualCone {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪x, y⟫_ℝ}

end ConeLifts.Shared
