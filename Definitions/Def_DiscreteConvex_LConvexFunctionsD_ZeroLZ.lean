import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[Z→R]`: L-convex functions on integer points whose convex extension is
positively homogeneous. -/
def ZeroLZ (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF g ∧ TRF g ∧ PosHomogeneous (fun p => ConvexClosureVal g p)

end DiscreteConvex.LConvexFunctionsD
