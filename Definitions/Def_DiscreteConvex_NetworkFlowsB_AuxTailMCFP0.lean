import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The tail map of the MCFP0 auxiliary network `Gξ`, on `Aξ = A*ξ ⊕ B*ξ`. -/
def AuxTailMCFP0 (tail head : A → V) : A ⊕ A → V
  | .inl a => tail a
  | .inr a => head a

end DiscreteConvex.NetworkFlowsB
