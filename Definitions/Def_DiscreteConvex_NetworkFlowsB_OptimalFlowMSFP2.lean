import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma2

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal flow for MSFP2. -/
def OptimalFlowMSFP2 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) : Prop :=
  FeasibleFlowMSFP2 tail head cUpper cLower f xi ∧
    ∀ xi', FeasibleFlowMSFP2 tail head cUpper cLower f xi' →
      Gamma2 tail head gamma f xi ≤ Gamma2 tail head gamma f xi'

end DiscreteConvex.NetworkFlowsB
