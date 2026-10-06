import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Membership in `Aξ = A*ξ ∪ B*ξ` (Eq. before (9.34)). -/
def AuxActiveMCFP0 (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (xi : A → ℝ) : A ⊕ A → Prop
  | .inl a => (xi a : WithTop ℝ) < cUpper a
  | .inr a => cLower a < (xi a : WithBot ℝ)

end DiscreteConvex.NetworkFlowsB
