import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the M-convex submodular flow problem MSFP2. -/
def FeasibleFlowMSFP2 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) : Prop :=
  (∀ a : A, cLower a ≤ (xi a : WithBot ℝ) ∧ (xi a : WithTop ℝ) ≤ cUpper a) ∧
    f (Boundary tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB
