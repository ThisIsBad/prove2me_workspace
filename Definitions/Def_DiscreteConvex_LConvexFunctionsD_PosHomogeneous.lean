import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is positively homogeneous. -/
def PosHomogeneous (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ t : ℝ, 0 < t → g (fun v => t * x v) = PosScalarMul t (g x)

end DiscreteConvex.LConvexFunctionsD
