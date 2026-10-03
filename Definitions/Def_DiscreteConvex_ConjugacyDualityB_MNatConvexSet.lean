import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M♮-convex: its lift is an M-convex set. -/
def MNatConvexSet (D : Set (V → ℤ)) : Prop := ExchangeAxiomB (LiftedSet D)

end DiscreteConvex.ConjugacyDualityB
