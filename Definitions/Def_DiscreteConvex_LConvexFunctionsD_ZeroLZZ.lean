import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValuedFn

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The class `0L[Z→Z]`: integer-valued members of `0L[Z→R]`. -/
def ZeroLZZ (g : (V → ℤ) → WithTop ℝ) : Prop := ZeroLZ g ∧ IsIntegerValuedFn g

end DiscreteConvex.LConvexFunctionsD
