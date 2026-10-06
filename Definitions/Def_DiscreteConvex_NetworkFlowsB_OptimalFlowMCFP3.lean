import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma3

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal flow for MCFP3 / MSFP3. -/
def OptimalFlowMCFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) : Prop :=
  FeasibleFlowMCFP3 tail head fa f xi ∧
    ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' → Gamma3 tail head fa f xi ≤ Gamma3 tail head fa f xi'

end DiscreteConvex.NetworkFlowsB
