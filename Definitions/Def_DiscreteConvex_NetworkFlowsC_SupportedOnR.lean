import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def SupportedOnR (S : Finset V) (x : V → ℝ) : Prop := ∀ v, v ∉ S → x v = 0

end DiscreteConvex.NetworkFlowsC
