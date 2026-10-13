import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90 (the "integral polyhedron" definition
preceding Eq. (3.50), reused at p.107, Eq. (4.30)-adjacent material): a real polyhedron is
integral if it is the convex hull of the integer points it contains, in
`DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- A polyhedron `P ⊆ Rⱽ` is **integral** if it coincides with the convex hull of the integer
points it contains: `P = conv(P ∩ Zⱽ)`, where `Zⱽ` is represented by its real embedding
`\{x : ∀v, ∃k:ℤ, x(v)=k\}`. -/
def IsIntegralPolyhedron {V : Type*} (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.MConvexSetsB
