import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LevelSet

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.72 (p.172). (QMw) is equivalent to (Q-EXCw) of every level set. -/
theorem qmw_iff_level_sets_qexcw (f : (V → ℤ) → WithTop ℝ) :
    QMw f ↔ ∀ alpha : ℝ, QEXCw (LevelSet f alpha) := by sorry

end DiscreteConvex.MConvexFunctionsE
