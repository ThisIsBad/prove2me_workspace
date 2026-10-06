import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `f : Rⱽ → R ∪ {+∞}` is polyhedral convex: its epigraph is a polyhedron. -/
def IsPolyhedralConvex (f : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedron (W := Option V)
    {p : Option V → ℝ | f (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.NetworkFlowsB
