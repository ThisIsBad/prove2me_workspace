import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def SuppPosR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.NetworkFlowsC
