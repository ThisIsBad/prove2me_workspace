import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Membership in `Aξ = A*ξ ∪ B*ξ ∪ Cξ` (Eq. (9.70)). -/
def AuxActiveMSFP2 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) : A ⊕ A ⊕ (V × V) → Prop
  | .inl a => (xi a : WithTop ℝ) < cUpper a
  | .inr (.inl a) => cLower a < (xi a : WithBot ℝ)
  | .inr (.inr (u, v)) => u ≠ v ∧ ∃ alpha : ℝ, 0 < alpha ∧
      f (fun w => Boundary tail head xi w -
        alpha * ((if w = u then (1:ℝ) else 0) - (if w = v then (1:ℝ) else 0))) ≠ ⊤

end DiscreteConvex.NetworkFlowsB
