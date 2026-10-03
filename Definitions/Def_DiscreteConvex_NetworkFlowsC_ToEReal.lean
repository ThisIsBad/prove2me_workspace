import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def ToEReal (v : WithTop ℝ) : EReal := WithBot.some v

end DiscreteConvex.NetworkFlowsC
