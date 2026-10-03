import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ExchangeAxiomB

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `Q ⊆ Zᴷ` is an M♮-convex set: the projection along a new coordinate of an M-convex set. -/
def IsMNaturalConvexSet (Q : Set (K → ℤ)) : Prop :=
  ∃ B : Set (Option K → ℤ), ExchangeAxiomB B ∧
    Q = {x : K → ℤ | ∃ x0 : ℤ, (fun w : Option K => w.elim x0 x) ∈ B}

-- ===== Concave/convex closures and the derived continuous economy (§11.4) =====

end DiscreteConvex.EconomicEquilibriumB
