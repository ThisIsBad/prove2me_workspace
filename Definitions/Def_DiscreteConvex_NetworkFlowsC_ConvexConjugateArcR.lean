import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The (real-variable) Legendre-Fenchel transform, univariate. -/
noncomputable def ConvexConjugateArcR (g : ℝ → WithTop ℝ) (s : ℝ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ t : ℝ, v = ((s * t : ℝ) : EReal) - ToEReal (g t)})

end DiscreteConvex.NetworkFlowsC
