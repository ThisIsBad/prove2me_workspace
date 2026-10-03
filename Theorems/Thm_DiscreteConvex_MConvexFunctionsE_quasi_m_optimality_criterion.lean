import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.76 (p.173-174). The quasi M-optimality criterion. -/
theorem quasi_m_optimality_criterion (f : (V → ℤ) → WithTop ℝ) :
    (QMw f → ∀ x ∈ DomZ f,
        ((∀ y : V → ℤ, y ≠ x → f x < f y) ↔ ∀ u v : V, u ≠ v → DeltaF f x v u > 0)) ∧
    (SSQMNeW f → ∀ x ∈ DomZ f,
        ((∀ y : V → ℤ, f x ≤ f y) ↔ ∀ u v : V, DeltaF f x v u ≥ 0)) := by sorry

end DiscreteConvex.MConvexFunctionsE
