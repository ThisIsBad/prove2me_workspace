import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Epi

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.99: a closed convex function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` is **closed convex** if `epi f` is a closed convex set. -/
def IsClosedConvexF {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  IsConvexF f ∧ IsClosed (Epi f)

end DiscreteConvex.IntegralConvexityB
