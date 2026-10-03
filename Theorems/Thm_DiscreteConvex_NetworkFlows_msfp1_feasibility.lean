import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMSFP1
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
import Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_Submodular
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

namespace DiscreteConvex.NetworkFlows

/-- Theorem 9.10, feasibility (Murota, *Discrete Convex Analysis*, SIAM 2003, p.258). A
submodular flow problem MSFP1 (upper capacity `c̄`, lower capacity `c`, submodular `ρ` with
`ρ(∅) = ρ(V) = 0`) is feasible if and only if `c̄(Δ⁻X) - c(Δ⁺X) + ρ(X) ≥ 0` for all `X ⊆ V`
(9.54). If `c̄`, `c`, and `ρ` are integer valued and the problem is feasible, an
integer-valued feasible flow exists. -/
theorem msfp1_feasibility {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (hρEmpty : ρ ∅ = 0)
    (hρV : ρ (Finset.univ : Finset V) = 0) :
    ((∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) ↔
      (∀ X : Finset V,
        UpperCapOf cUpper (DeltaMinus tail head X) +
            NegLowerCapOf cLower (DeltaPlus tail head X) + ρ X ≥ 0)) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → IsIntegerUpper ρ →
      (∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) →
      ∃ ξ : A → ℤ, FeasibleFlowMSFP1 tail head cUpper cLower ρ (fun a => (ξ a : ℝ))) := by sorry

end DiscreteConvex.NetworkFlows
