import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.4 (Potential criterion; p.249-250). GOAL. In the minimum cost flow problem MCFP3
with polyhedral convex `f` and `fa` (`a ∈ A`): (1) for a feasible flow `ξ`, `ξ` is optimal iff
there is a potential `p` satisfying (i)-(ii) of (POT); (2) any optimal potential for one optimal
flow characterizes optimality of every feasible flow. -/
theorem potential_criterion_mcfp3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hfa : ∀ a, IsPolyhedralConvexArc (fa a)) :
    (∀ xi, FeasibleFlowMCFP3 tail head fa f xi →
      (OptimalFlowMCFP3 tail head fa f xi ↔ ∃ p : V → ℝ, IsOptimalPotential tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMCFP3 tail head fa f xi → IsOptimalPotential tail head fa f xi p →
      ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' →
        (OptimalFlowMCFP3 tail head fa f xi' ↔ IsOptimalPotential tail head fa f xi' p)) := by sorry

end DiscreteConvex.NetworkFlowsB

