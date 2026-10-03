import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def MNaturalConvexR (f : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR (LiftedFunctionR f)

end DiscreteConvex.NetworkFlowsC
