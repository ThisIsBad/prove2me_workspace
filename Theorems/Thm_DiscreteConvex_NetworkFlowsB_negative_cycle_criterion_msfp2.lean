import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_HasNegativeCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.18 (Negative-cycle criterion for MSFP2; p.263-264). For a feasible flow `ξ` to
MSFP2 with M-convex `f`, `ξ` is optimal iff the auxiliary network `(Gξ, ℓξ)` has no negative
cycle. -/
theorem negative_cycle_criterion_msfp2 (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f)
    (xi : A → ℝ) (hfeas : FeasibleFlowMSFP2 tail head cUpper cLower f xi) :
    OptimalFlowMSFP2 tail head cUpper cLower gamma f xi ↔
      ¬ HasNegativeCycle (AuxTailMSFP2 tail head) (AuxHeadMSFP2 tail head)
        (AuxActiveMSFP2 tail head cUpper cLower f xi) (AuxLengthMSFP2 tail head gamma f xi) := by sorry

end DiscreteConvex.NetworkFlowsB

