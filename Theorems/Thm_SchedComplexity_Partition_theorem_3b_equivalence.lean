import Mathlib
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Theorem 3(b) (p. 15): for positive integers `a_1, …, a_t`, PARTITION has a solution iff the
two-identical-machine instance `n = t`, `p_{j1} = w_j = a_j` has a feasible schedule with
`Σ w_j C_j ≤ y = Σ_{j,k∈T, j≤k} a_j a_k − ¼A²`. -/
theorem theorem_3b_equivalence (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    PartitionSolvable a ↔
      ∃ σ : Schedule a.length, σ.IsFeasible (procB a) ∧
        (σ.sumWC (procB a) (procB a) : ℝ) ≤ yB a := by sorry

end SchedComplexity.Partition

