import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The arc-length function `ℓξ` of Eq. (9.34). -/
def AuxLengthMCFP0 (gamma : A → ℝ) : A ⊕ A → WithTop ℝ
  | .inl a => (gamma a : WithTop ℝ)
  | .inr a => ((-gamma a : ℝ) : WithTop ℝ)

-- ===== MSFP2 (linear arc cost, M-convex boundary cost) =====

end DiscreteConvex.NetworkFlowsB
