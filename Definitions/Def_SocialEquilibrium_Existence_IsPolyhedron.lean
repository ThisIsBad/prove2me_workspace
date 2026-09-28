import Mathlib

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 887: a *convex cell* is the set of all convex combinations of finitely
many (at least one) points `z¹, …, zʳ`, i.e. the convex hull of a nonempty finite set. -/
def IsConvexCell {E : Type*} [AddCommGroup E] [Module ℝ E] (C : Set E) : Prop :=
  ∃ s : Finset E, s.Nonempty ∧ C = convexHull ℝ (↑s : Set E)

/-- Debreu (1952), §1, p. 887: a *geometric polyhedron* is the union of a finite number of
convex cells. -/
def IsGeometricPolyhedron {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ S : Finset (Set E), (∀ C ∈ S, IsConvexCell C) ∧ P = ⋃ C ∈ S, C

/-- Debreu (1952), §1, p. 887: a *polyhedron* is a set homeomorphic (as a topological subspace)
to a geometric polyhedron (its *geometric antecedent*) lying in some finite Euclidean space
`ℝᵐ`. -/
def IsPolyhedron {E : Type*} [TopologicalSpace E] (P : Set E) : Prop :=
  ∃ (m : ℕ) (Q : Set (EuclideanSpace ℝ (Fin m))), IsGeometricPolyhedron Q ∧ Nonempty (P ≃ₜ Q)

end SocialEquilibrium.Existence
