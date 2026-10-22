import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_InfPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_CastZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Proposition 3.30, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.30.** For an integer-valued integrally convex function
`f : Zⁿ → Z∪{+∞}` and `p ∈ Rⁿ`, `arg min f[-p] ≠ ∅` if `inf f[-p] > -∞`. -/
theorem prop_3_30_argmin_nonempty_integer_valued {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ)
    (hic : IntegrallyConvex (CastZR f)) (p : Fin n → ℝ)
    (hinf : InfPerturbed (CastZR f) p > ⊥) :
    (ArgMinPerturbed (CastZR f) p).Nonempty := by sorry

end DiscreteConvex.IntegralConvexityC

