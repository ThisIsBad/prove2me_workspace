import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate function `g : R → R ∪ {+∞}` is polyhedral convex. -/
def IsPolyhedralConvexArc (g : ℝ → WithTop ℝ) : Prop :=
  IsPolyhedron (W := Bool) {p : Bool → ℝ | g (p false) ≤ ((p true : ℝ) : WithTop ℝ)}

end DiscreteConvex.NetworkFlowsB
