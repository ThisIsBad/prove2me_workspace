import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BipartiteMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MatchingWeight

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def IsMinWeightMatching (Vp Vn : Finset V) (c : V → V → WithTop ℝ) (M : Finset (V × V)) : Prop :=
  BipartiteMatching Vp Vn M ∧
    ∀ M', BipartiteMatching Vp Vn M' → MatchingWeight c M ≤ MatchingWeight c M'

end DiscreteConvex.NetworkFlowsC
