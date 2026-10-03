import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The characteristic vector of `v`. -/
def CharVec (v : V) : V → ℤ := fun w => if w = v then 1 else 0

end DiscreteConvex.MConvexFunctionsE
