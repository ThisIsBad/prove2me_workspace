import Mathlib

namespace ConeLifts.StableSet

/-- `C` **has a `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.1, p. 3):
there are an affine subspace `L` of the ambient space of `K` and a *linear* map `π` with
`C = π(K ∩ L)` (equality of sets); `Q = K ∩ L` is then a `K`-lift of `C`. The paper's standing
hypotheses on `K` (full-dimensional closed convex cone) and on `C` are carried by the theorems
that use this predicate; the predicate itself is stated for arbitrary real vector spaces so that
it covers both `K ⊆ ℝᵐ` and the cone of positive semidefinite matrices. -/
def HasConeLift {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (K : Set V) (C : Set W) : Prop :=
  ∃ (L : AffineSubspace ℝ V) (π : V →ₗ[ℝ] W), C = π '' (K ∩ (L : Set V))

/-- `C` **has a proper `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.1,
p. 3): a `K`-lift `C = π(K ∩ L)` whose affine subspace `L` intersects the interior of `K`. -/
def HasProperConeLift {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] (K : Set V) (C : Set W) : Prop :=
  ∃ (L : AffineSubspace ℝ V) (π : V →ₗ[ℝ] W),
    C = π '' (K ∩ (L : Set V)) ∧ ((L : Set V) ∩ interior K).Nonempty

end ConeLifts.StableSet
