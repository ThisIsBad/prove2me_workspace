import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def MatchingWeight (c : V → V → WithTop ℝ) (M : Finset (V × V)) : WithTop ℝ :=
  ∑ p ∈ M, c p.1 p.2

end DiscreteConvex.NetworkFlowsC
