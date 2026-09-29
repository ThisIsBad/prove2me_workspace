import Mathlib

namespace ConeLifts.Factorization

/-- `K ⊆ ℝᵐ` is a **closed convex cone** (the class of cones of Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 2.1, p. 3): `K` is topologically closed, convex, contains the
origin, and is closed under multiplication by nonnegative scalars. Pointedness (salience) is not
required. Full-dimensionality, which Definition 2.1 also asks for, is the separate hypothesis
`(interior K).Nonempty`. -/
def IsClosedConvexCone {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  IsClosed K ∧ Convex ℝ K ∧ (0 : EuclideanSpace ℝ (Fin m)) ∈ K ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K

end ConeLifts.Factorization
