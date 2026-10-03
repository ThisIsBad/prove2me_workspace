import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_SeparableConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Proposition 3.24, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.24.** The sum of an integrally convex function and a separable convex
function is an integrally convex function. -/
theorem prop_3_24_sum_integrally_convex_separable {n : ℕ} (f0 fsep : (Fin n → ℤ) → WithTop ℝ)
    (h0 : IntegrallyConvex f0) (hsep : SeparableConvex fsep) :
    IntegrallyConvex (fun x => f0 x + fsep x) := by sorry

end DiscreteConvex.IntegralConvexityC
