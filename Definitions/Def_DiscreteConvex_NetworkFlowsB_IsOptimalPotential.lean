import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedArcCost
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedBoundaryCost

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `p` is an optimal potential for the flow `ξ`: conditions (i) and (ii) of (POT). -/
def IsOptimalPotential (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (p : V → ℝ) : Prop :=
  (∀ a : A, xi a ∈ ArgMinArc (ReducedArcCost tail head fa p a)) ∧
    Boundary tail head xi ∈ ArgMinR (ReducedBoundaryCost f p)

end DiscreteConvex.NetworkFlowsB
