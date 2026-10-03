import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverBot
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97: a proper convex function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- A **proper convex function**: convex, never `-∞`, with nonempty effective domain. -/
def IsProperConvex {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  IsConvexF f ∧ NeverBot f ∧ (DomE f).Nonempty

end DiscreteConvex.IntegralConvexityB
