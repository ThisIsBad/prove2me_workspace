import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def CharVec (u : V) : V → ℤ := fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexFunctionsC
