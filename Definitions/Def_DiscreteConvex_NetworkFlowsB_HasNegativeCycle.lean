import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsCycle
import Definitions.Def_DiscreteConvex_NetworkFlowsB_CycleLength

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- There exists a negative-length cycle using only `active` arcs. -/
def HasNegativeCycle {Arc W : Type*} (tail head : Arc → W) (active : Arc → Prop)
    (l : Arc → WithTop ℝ) : Prop :=
  ∃ (k : ℕ) (a : Fin (k+1) → Arc), (∀ i, active (a i)) ∧ IsCycle tail head k a ∧
    CycleLength l k a < 0

end DiscreteConvex.NetworkFlowsB
