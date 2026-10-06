import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for MCFP0, via its MCFP3 encoding. -/
def FeasibleFlowMCFP0 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ) : Prop :=
  FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi

end DiscreteConvex.NetworkFlowsB
