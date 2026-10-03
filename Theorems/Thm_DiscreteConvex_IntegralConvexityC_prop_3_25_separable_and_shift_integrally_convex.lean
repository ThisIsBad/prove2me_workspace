import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_SeparableConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96, Proposition 3.25, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.25.** (1) A separable convex function is integrally convex.
(2) `f[-p]` is integrally convex for integrally convex `f` and vector `p ∈ Rⁿ`. -/
theorem prop_3_25_separable_and_shift_integrally_convex {n : ℕ} :
    (∀ f : (Fin n → ℤ) → WithTop ℝ, SeparableConvex f → IntegrallyConvex f) ∧
      (∀ f : (Fin n → ℤ) → WithTop ℝ, IntegrallyConvex f → ∀ p : Fin n → ℝ,
        IntegrallyConvex (fun x => f x - ((∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ))) := by sorry

end DiscreteConvex.IntegralConvexityC
