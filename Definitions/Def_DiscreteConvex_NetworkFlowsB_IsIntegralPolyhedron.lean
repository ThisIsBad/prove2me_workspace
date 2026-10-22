import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A polyhedron `P ⊆ Rⱽ` is integral if it coincides with the convex hull of the integer points
it contains. -/
def IsIntegralPolyhedron (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.NetworkFlowsB
