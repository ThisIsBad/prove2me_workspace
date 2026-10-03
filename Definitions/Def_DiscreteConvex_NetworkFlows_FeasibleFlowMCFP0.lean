import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_Boundary

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.248, Eqs. (9.12)-(9.13): feasibility for the
minimum cost flow problem MCFP0, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A flow `ξ : A → ℝ` is **feasible for MCFP0** with upper capacity `c̄`, lower capacity `c`,
and supply `x` if it meets the capacity constraint (9.12) and has boundary `x` (9.13). -/
def FeasibleFlowMCFP0 {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (x : V → ℝ)
    (ξ : A → ℝ) : Prop :=
  (∀ a : A, cLower a ≤ (ξ a : WithBot ℝ) ∧ (ξ a : WithTop ℝ) ≤ cUpper a) ∧
    ∀ v : V, Boundary tail head ξ v = x v

end DiscreteConvex.NetworkFlows
