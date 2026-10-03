import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[R→R]`: polyhedral L-convex, positively homogeneous functions. -/
def ZeroLR (g : (V → ℝ) → WithTop ℝ) : Prop := SBFR g ∧ TRFR g ∧ PosHomogeneous g

end DiscreteConvex.LConvexFunctionsD
