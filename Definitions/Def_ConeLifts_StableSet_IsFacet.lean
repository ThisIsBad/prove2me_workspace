import Mathlib

namespace ConeLifts.StableSet

/-- `F` is a **facet** of the convex set `P ⊆ ℝⁿ` (the notion used in Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, §3, p. 9, and in the proof of Theorem 5.2, p. 19): `F` is a nonempty proper
exposed face of `P` (the set where some linear functional attains its maximum over `P`) whose
affine dimension is one less than that of `P`. Dimensions are compared as
`dim F + 1 = dim P` with `dim` the rank of the vector span; since `F` is required to be nonempty,
no truncated subtraction or empty-set convention is involved. -/
def IsFacet {n : ℕ} (P F : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
    Module.finrank ℝ (vectorSpan ℝ F) + 1 = Module.finrank ℝ (vectorSpan ℝ P)

end ConeLifts.StableSet
