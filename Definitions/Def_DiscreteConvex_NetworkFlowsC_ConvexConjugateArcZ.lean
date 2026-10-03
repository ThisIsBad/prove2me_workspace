import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The discrete Legendre-Fenchel transform, univariate integer domain. -/
noncomputable def ConvexConjugateArcZ (g : ℤ → WithTop ℝ) (s : ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ t : ℤ, v = (((s * t : ℤ) : ℝ) : EReal) - ToEReal (g t)})

-- ===== Base vocabulary, real domain (redeclared) =====

end DiscreteConvex.NetworkFlowsC
