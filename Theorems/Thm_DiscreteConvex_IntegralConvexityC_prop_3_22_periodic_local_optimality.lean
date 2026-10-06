import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IndicatorVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Proposition 3.22, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- **Proposition 3.22.** Let `f : Zⁿ → R∪{+∞}` be integrally convex with `f(z+1) = f(z)` for
all `z`. For `x ∈ dom_Z f`, `f(x) ≤ f(y)` for all `y` iff `f(x) ≤ f(x+χ_Y)` for all
`Y ⊆ \{1,…,n\}`. -/
theorem prop_3_22_periodic_local_optimality {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hic : IntegrallyConvex f) (hper : ∀ z : Fin n → ℤ, f (z + fun _ => (1 : ℤ)) = f z)
    (x : Fin n → ℤ) (hx : x ∈ DomZ f) :
    (∀ y : Fin n → ℤ, f x ≤ f y) ↔
      (∀ Y : Finset (Fin n), f x ≤ f (x + IndicatorVec Y)) := by sorry

end DiscreteConvex.IntegralConvexityC

