import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M2-convex: the intersection of two M-convex sets. -/
def M2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), ExchangeAxiomB D1 ∧ ExchangeAxiomB D2 ∧ D = D1 ∩ D2

end DiscreteConvex.ConjugacyDualityB
