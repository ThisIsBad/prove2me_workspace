import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_AllocationInstance

namespace OnlinePrimalDual.BoundedAllocation

/-- The value (total seller profit) of a fractional allocation `y`, the packing/dual objective
of Fig. 13.1: `∑_j ∑_{i∈S(j)} b(j)y(i,j)`. -/
def packingValue {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : AllocationInstance I J) (y : I → J → ℝ) : ℝ :=
  ∑ j, ∑ i ∈ inst.S j, inst.b j * y i j

end OnlinePrimalDual.BoundedAllocation
