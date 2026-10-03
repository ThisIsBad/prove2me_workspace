import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `x` is supported on `S`: `x(v) = 0` for `v ∉ S`. -/
def SupportedOn (S : Finset V) (x : V → ℤ) : Prop := ∀ v, v ∉ S → x v = 0

end DiscreteConvex.NetworkFlowsC
