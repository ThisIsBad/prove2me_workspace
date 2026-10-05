import Mathlib

namespace ConeLifts.Factorization

/-- `C ⊆ ℝⁿ` **has a proper `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 2.1, p. 3): there are an affine subspace `L ⊆ ℝᵐ` and a linear map `π : ℝᵐ → ℝⁿ`
with `C = π(K ∩ L)` such that `L` intersects the interior of `K`. -/
def HasProperLift {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
    C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))) ∧
      (interior K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))).Nonempty

end ConeLifts.Factorization
