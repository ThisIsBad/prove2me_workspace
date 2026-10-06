import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The head map of the MSFP2 auxiliary network. -/
def AuxHeadMSFP2 (tail head : A → V) : A ⊕ A ⊕ (V × V) → V
  | .inl a => head a
  | .inr (.inl a) => tail a
  | .inr (.inr (_, v)) => v

end DiscreteConvex.NetworkFlowsB
