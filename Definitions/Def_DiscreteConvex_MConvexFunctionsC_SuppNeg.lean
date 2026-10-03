import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctionsC
