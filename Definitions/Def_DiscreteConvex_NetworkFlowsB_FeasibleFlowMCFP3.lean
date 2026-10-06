import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the (nonlinear-cost) minimum cost flow problem MCFP3 / the M-convex
submodular flow problem MSFP3. -/
def FeasibleFlowMCFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) : Prop :=
  (∀ a : A, fa a (xi a) ≠ ⊤) ∧ f (Boundary tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB
