import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedGTildeWT (tail head : A → V) (S T : Finset V) (ga : A → ℤ → WithTop ℝ)
    (g : (V → ℤ) → WithTop ℝ) (q : V → ℤ) : WithTop ℝ :=
  FromEReal (InducedGTilde tail head S T ga g q)

-- ===== Network transformation apparatus (§9.6), real domain =====

end DiscreteConvex.NetworkFlowsC
