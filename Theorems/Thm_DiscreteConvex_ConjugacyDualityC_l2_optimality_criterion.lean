import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.43 (L2-optimality criterion; p.232). Global optimality of an L2-convex function is
characterized by local non-improvement plus periodicity. -/
theorem l2_optimality_criterion (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g) (p : V → ℤ)
    (hp : p ∈ DomZ g) :
    (∀ q, g p ≤ g q) ↔
      ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧ g p = g (p + 1)) := by sorry

end DiscreteConvex.ConjugacyDualityC

