import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_AllocationInstance

namespace OnlinePrimalDual.BoundedAllocation

/-- Feasibility for the fractional packing (dual) LP of Fig. 13.1: `y i j` is the fraction of
item `j` allocated to buyer `i`, non-negative, each item fully allocated at most once
(`∀j, ∑_{i∈S(j)} y(i,j) ≤ 1`), and each buyer's budget respected
(`∀i, ∑_{j|i∈S(j)} b(j)y(i,j) ≤ B(i)`). -/
def packingFeasible {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : AllocationInstance I J) (y : I → J → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧
  (∀ j, ∑ i ∈ inst.S j, y i j ≤ 1) ∧
  (∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), inst.b j * y i j ≤ inst.B i)

end OnlinePrimalDual.BoundedAllocation
