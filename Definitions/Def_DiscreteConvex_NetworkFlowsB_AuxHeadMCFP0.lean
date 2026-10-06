import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The head map of the MCFP0 auxiliary network `Gξ`. -/
def AuxHeadMCFP0 (tail head : A → V) : A ⊕ A → V
  | .inl a => head a
  | .inr a => tail a

end DiscreteConvex.NetworkFlowsB
