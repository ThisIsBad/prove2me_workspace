import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedGTildeRWT (tail head : A → V) (S T : Finset V) (ga : A → ℝ → WithTop ℝ)
    (g : (V → ℝ) → WithTop ℝ) (q : V → ℝ) : WithTop ℝ :=
  FromEReal (InducedGTildeR tail head S T ga g q)

-- ===== Bipartite matching and the unique-min condition (§9.5.2) =====

end DiscreteConvex.NetworkFlowsC
