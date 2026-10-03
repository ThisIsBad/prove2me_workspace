import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeqW

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Theorem 6.76, the quasi M-optimality criterion (Murota, *Discrete Convex Analysis*, SIAM
2003, p.173). (1) For `f` satisfying (QMw) and `x ∈ dom f`, `f(x) < f(y)` for all `y ≠ x` iff
`f(x) < f(x - χ_u + χ_v)` for all `u, v ∈ V` with `u ≠ v`. (2) For `f` satisfying (SSQM≠_w) and
`x ∈ dom f`, `f(x) ≤ f(y)` for all `y` iff `f(x) ≤ f(x - χ_u + χ_v)` for all `u, v ∈ V`. -/
theorem quasi_m_optimality_criterion {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, QMw f → ∀ x ∈ DomZ f,
      (∀ y : V → ℤ, y ≠ x → f x < f y) ↔
        (∀ u v : V, u ≠ v → f x < f (fun w => x w - CharVec u w + CharVec v w))) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, SSQMNeqW f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔
        (∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w))) := by sorry

end DiscreteConvex.MConvexFunctions.Quasi
