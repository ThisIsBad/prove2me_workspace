import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ExchangeAxiomB

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `D` is M2-convex: the intersection of two M-convex sets. -/
def M2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), ExchangeAxiomB D1 ∧ ExchangeAxiomB D2 ∧ D = D1 ∩ D2

end DiscreteConvex.NetworkFlowsB
