import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of boundaries of optimal integer flows for MSFP3. -/
def BoundaryOptSetMSFP3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ) :
    Set (V → ℤ) :=
  {x | ∃ xi, OptimalFlowMSFP3Z tail head fa f xi ∧ x = BoundaryZ tail head xi}

end DiscreteConvex.NetworkFlowsB
