import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IsBoundedZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97, Theorem 3.29 — the goal of this mission —
in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Theorem 3.29** (goal). Suppose `f : Zⁿ → R∪{+∞}` has a nonempty bounded effective domain.
Then `f` is integrally convex iff `arg min f[-p]` is an integrally convex set for every
`p ∈ Rⁿ`. -/
theorem theorem_3_29_integrally_convex_iff_argmin_sets {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hne : (DomZ f).Nonempty) (hbdd : IsBoundedZ (DomZ f)) :
    IntegrallyConvex f ↔ ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) := by sorry

end DiscreteConvex.IntegralConvexityC

