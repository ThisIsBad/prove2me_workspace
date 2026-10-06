import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
import Definitions.Def_DiscreteConvex_IntegralConvexityB_MatchingWeight

/-!
A minimum-weight perfect matching (Murota, *Discrete Convex Analysis*, SIAM 2003, p.109), in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `σ` is a **minimum-weight perfect matching** of `(Vp, Vm; E)` for cost `c`. -/
def IsMinWeightMatching {Vp Vm : Type*} [Fintype Vp] (E : Set (Vp × Vm)) (c : Vp × Vm → WithTop ℝ)
    (sigma : Vp ≃ Vm) : Prop :=
  IsPerfectMatchingBij E sigma ∧
    ∀ tau : Vp ≃ Vm, IsPerfectMatchingBij E tau → MatchingWeight c sigma ≤ MatchingWeight c tau

end DiscreteConvex.IntegralConvexityB
