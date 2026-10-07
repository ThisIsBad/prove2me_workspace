import Mathlib
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Theorem 3(a) (p. 15): for positive integers `a_1, …, a_t`, PARTITION has a solution iff the
two-identical-machine instance `n = t`, `p_{j1} = a_j` has a feasible schedule with
`C_max ≤ y = ½A`. -/
theorem theorem_3a_equivalence (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    PartitionSolvable a ↔
      ∃ σ : Schedule a.length, σ.IsFeasible (procA a) ∧
        ∀ j, (σ.completion (procA a) j : ℝ) ≤ yA a := by sorry

end SchedComplexity.Partition

