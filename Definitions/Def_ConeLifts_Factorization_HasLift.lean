import Mathlib

namespace ConeLifts.Factorization

/-- `C ⊆ ℝⁿ` **has a `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.1,
p. 3): there are an affine subspace `L ⊆ ℝᵐ` and a *linear* map `π : ℝᵐ → ℝⁿ` with
`C = π(K ∩ L)`; the set `Q = K ∩ L` is then a `K`-lift of `C`. The standing hypotheses of
Definition 2.1 on `K` (full-dimensional closed convex cone) and `C` (convex body) are carried by
the theorems that use this predicate. -/
def HasLift {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (C : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  ∃ (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
    C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m))))

end ConeLifts.Factorization
