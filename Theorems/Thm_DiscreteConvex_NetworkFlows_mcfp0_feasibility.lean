import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlows_CutCapacity
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

namespace DiscreteConvex.NetworkFlows

/-- Theorem 9.3, feasibility (Murota, *Discrete Convex Analysis*, SIAM 2003, p.248). For
`c̄ : A → ℝ ∪ {+∞}`, `c : A → ℝ ∪ {-∞}`, and `x : V → ℝ`, there exists a flow `ξ : A → ℝ`
satisfying the capacity constraint (9.12) and `∂ξ = x` (9.13) if and only if `x(X) ≤ κ(X)`
for all `X ⊆ V` and `x(V) = 0`. If `c̄` and `c` are integer valued, `x` is integer valued, and
the problem is feasible, an integer-valued feasible flow exists. -/
theorem mcfp0_feasibility {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (x : V → ℝ) :
    ((∃ ξ : A → ℝ, FeasibleFlowMCFP0 tail head cUpper cLower x ξ) ↔
      ((∀ X : Finset V,
          ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ CutCapacity tail head cUpper cLower X) ∧
        (∑ v : V, x v) = 0)) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → (∀ v : V, ∃ n : ℤ, (n : ℝ) = x v) →
      (∃ ξ : A → ℝ, FeasibleFlowMCFP0 tail head cUpper cLower x ξ) →
      ∃ ξ : A → ℤ, FeasibleFlowMCFP0 tail head cUpper cLower x (fun a => (ξ a : ℝ))) := by sorry

end DiscreteConvex.NetworkFlows
