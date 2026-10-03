import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionRL

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def LNaturalConvexR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  SBFR (LiftedFunctionRL g) ∧ TRFR (LiftedFunctionRL g)

end DiscreteConvex.NetworkFlowsC
