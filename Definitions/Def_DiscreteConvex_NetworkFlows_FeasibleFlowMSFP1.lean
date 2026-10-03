import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_Boundary

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.258, Eqs. (9.52)-(9.53): feasibility for the
submodular flow problem MSFP1, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A flow `ξ : A → ℝ` is **feasible for MSFP1** with upper capacity `c̄`, lower capacity `c`,
and submodular function `ρ` if it meets the capacity constraint (9.52) and its boundary lies
in the base polyhedron `B(ρ)` (9.53), i.e. `∂ξ(X) ≤ ρ(X)` for every `X ⊆ V` and `∂ξ(V) = 0`. -/
def FeasibleFlowMSFP1 {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (ξ : A → ℝ) : Prop :=
  (∀ a : A, cLower a ≤ (ξ a : WithBot ℝ) ∧ (ξ a : WithTop ℝ) ≤ cUpper a) ∧
    (∀ X : Finset V, ((∑ v ∈ X, Boundary tail head ξ v : ℝ) : WithTop ℝ) ≤ ρ X) ∧
    (∑ v : V, Boundary tail head ξ v) = 0

end DiscreteConvex.NetworkFlows
