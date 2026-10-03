import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConjF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverBot

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.102, Theorem 3.2, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.2.** The Legendre-Fenchel transform `f•` is a closed proper convex function for
any `f` with `dom f ≠ ∅`, and `f•• = f` for a closed proper convex function `f`. -/
theorem theorem_3_2_biconjugate {V : Type*} [Fintype V] (f : (V → ℝ) → EReal)
    (hdom : (DomE f).Nonempty) (hnb : NeverBot f) :
    (IsProperConvex (ConjF f) ∧ IsClosedConvexF (ConjF f)) ∧
      (∀ g : (V → ℝ) → EReal, IsClosedConvexF g → IsProperConvex g →
        ConjF (ConjF g) = g) := by sorry

end DiscreteConvex.IntegralConvexityB
