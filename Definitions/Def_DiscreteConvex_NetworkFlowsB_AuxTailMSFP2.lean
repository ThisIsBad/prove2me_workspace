import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The tail map of the MSFP2 auxiliary network, on `Aξ = A*ξ ⊕ B*ξ ⊕ Cξ`. -/
def AuxTailMSFP2 (tail head : A → V) : A ⊕ A ⊕ (V × V) → V
  | .inl a => tail a
  | .inr (.inl a) => head a
  | .inr (.inr (u, _)) => u

end DiscreteConvex.NetworkFlowsB
