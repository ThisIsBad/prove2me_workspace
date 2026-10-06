import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IndicatorZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96: an integrally convex set, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `S ⊆ Zⁿ` is **integrally convex** if its indicator function `δ_S` is an integrally convex
function. -/
noncomputable def IntegrallyConvexSet {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  IntegrallyConvex (IndicatorZ S)

end DiscreteConvex.IntegralConvexityC
