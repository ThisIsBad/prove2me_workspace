import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNatConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M♮₂-convex: the intersection of two M♮-convex sets. -/
def MNat2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), MNatConvexSet D1 ∧ MNatConvexSet D2 ∧ D = D1 ∩ D2

end DiscreteConvex.ConjugacyDualityB
