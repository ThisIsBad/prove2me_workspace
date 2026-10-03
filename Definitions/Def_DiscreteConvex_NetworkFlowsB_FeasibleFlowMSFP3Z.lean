import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the M-convex submodular integer-flow problem MSFP3. -/
def FeasibleFlowMSFP3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) : Prop :=
  (∀ a : A, fa a (xi a) ≠ ⊤) ∧ f (BoundaryZ tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB
