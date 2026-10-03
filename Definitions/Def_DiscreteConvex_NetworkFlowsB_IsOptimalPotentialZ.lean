import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMinArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArgMin
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedArcCostZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ReducedBoundaryCostZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `p` is an optimal potential for the integer flow `ξ`. -/
def IsOptimalPotentialZ (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) (p : V → ℝ) : Prop :=
  (∀ a : A, xi a ∈ ArgMinArcZ (ReducedArcCostZ tail head fa p a)) ∧
    BoundaryZ tail head xi ∈ ArgMin (ReducedBoundaryCostZ f p)

end DiscreteConvex.NetworkFlowsB
