import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.104, Eq. (4.13): the base polyhedron of a
submodular set function, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The **base polyhedron** `B(ρ) = \{x ∈ Rⱽ : x(X) ≤ ρ(X)\ (∀X ⊆ V),\ x(V) = ρ(V)\}` of a
submodular set function `ρ` (Eq. (4.13)). -/
def BasePolyhedron {V : Type*} [Fintype V] [DecidableEq V] (ρ : Finset V → WithTop ℝ) :
    Set (V → ℝ) :=
  {x | (∀ X : Finset V, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ X) ∧
    ((∑ v : V, x v : ℝ) : WithTop ℝ) = ρ Finset.univ}

end DiscreteConvex.MConvexSetsB
