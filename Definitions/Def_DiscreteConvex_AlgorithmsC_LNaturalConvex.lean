import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_SBF
import Definitions.Def_DiscreteConvex_AlgorithmsC_TRF
import Definitions.Def_DiscreteConvex_AlgorithmsC_LiftedFunctionL

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.AlgorithmsC
