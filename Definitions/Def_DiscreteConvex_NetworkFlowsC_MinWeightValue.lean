import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BipartiteMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MatchingWeight

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The minimum weight of a perfect matching, `+∞` if none exists. -/
noncomputable def MinWeightValue (Vp Vn : Finset V) (c : V → V → WithTop ℝ) : WithTop ℝ :=
  sInf {w : WithTop ℝ | ∃ M, BipartiteMatching Vp Vn M ∧ w = MatchingWeight c M}

end DiscreteConvex.NetworkFlowsC
