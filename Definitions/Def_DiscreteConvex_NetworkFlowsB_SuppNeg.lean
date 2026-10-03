import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The negative support, integer-vector version. -/
def SuppNeg (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.NetworkFlowsB
