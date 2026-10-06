import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.109: a perfect matching of a bipartite graph,
represented as a bijection between the two sides, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- A **perfect matching** of the bipartite graph `(Vp, Vm; E)`, represented as a bijection
`σ : Vp ≃ Vm` all of whose pairs `(u, σ u)` are arcs of `E`. -/
def IsPerfectMatchingBij {Vp Vm : Type*} (E : Set (Vp × Vm)) (sigma : Vp ≃ Vm) : Prop :=
  ∀ u, (u, sigma u) ∈ E

end DiscreteConvex.IntegralConvexityB
