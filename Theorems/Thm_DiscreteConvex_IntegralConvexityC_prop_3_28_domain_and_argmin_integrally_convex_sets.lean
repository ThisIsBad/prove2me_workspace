import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97, Proposition 3.28, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.28.** Let `f : Zⁿ → R∪{+∞}` be integrally convex. (1) `dom_Z f` is an
integrally convex set. (2) For each `p ∈ Rⁿ`, `arg min f[-p]` is an integrally convex set. -/
theorem prop_3_28_domain_and_argmin_integrally_convex_sets {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hf : IntegrallyConvex f) :
    IntegrallyConvexSet (DomZ f) ∧
      ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) := by sorry

end DiscreteConvex.IntegralConvexityC

