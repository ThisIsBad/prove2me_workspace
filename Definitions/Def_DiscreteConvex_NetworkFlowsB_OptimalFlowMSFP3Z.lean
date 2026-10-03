import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma3Z

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal integer flow for MSFP3. -/
def OptimalFlowMSFP3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) : Prop :=
  FeasibleFlowMSFP3Z tail head fa f xi ∧
    ∀ xi', FeasibleFlowMSFP3Z tail head fa f xi' →
      Gamma3Z tail head fa f xi ≤ Gamma3Z tail head fa f xi'

end DiscreteConvex.NetworkFlowsB
