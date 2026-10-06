import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMCFP0

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.5 (Negative-cycle criterion; p.252). For a feasible flow `ξ` to MCFP0, `ξ` is
optimal iff the auxiliary network `(Gξ, ℓξ)` has no negative cycle. -/
theorem negative_cycle_criterion_mcfp0 (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (hfeas : FeasibleFlowMCFP0 tail head cUpper cLower gamma x xi) :
    OptimalFlowMCFP0 tail head cUpper cLower gamma x xi ↔
      ¬ HasNegativeCycle (AuxTailMCFP0 tail head) (AuxHeadMCFP0 tail head)
        (AuxActiveMCFP0 cUpper cLower xi) (AuxLengthMCFP0 gamma) := by sorry

end DiscreteConvex.NetworkFlowsB

