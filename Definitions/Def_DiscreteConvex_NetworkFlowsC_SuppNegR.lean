import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def SuppNegR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.NetworkFlowsC
