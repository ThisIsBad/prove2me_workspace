import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The (real-variable) Legendre-Fenchel transform. -/
noncomputable def ConvexConjugateR (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℝ,
    v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.NetworkFlowsC
