import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMSFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ArcCostMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of optimal potentials for MCFP0. -/
def OptimalPotentialSetMCFP0 (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (x : V → ℝ) : Set (V → ℝ) :=
  OptimalPotentialSetMSFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x)

-- ===== Auxiliary networks and negative cycles (shared machinery) =====

end DiscreteConvex.NetworkFlowsB
