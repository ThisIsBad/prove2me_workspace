import Mathlib
import Definitions.Def_SchedComplexity_Partition_TwoMachineModel
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Proof of Theorem 3(b) (p. 15): in construction (b) (`p_{j1} = w_j = a_j`), let `S` be the set
of jobs assigned to `M_1` (machine `0`) and `T − S` those on `M_2`. If each machine works without
idle time from `0`, then `Σ w_j C_j = k(S)` whatever the order of the jobs; every feasible
schedule with this assignment has `Σ w_j C_j ≥ k(S)`. -/
theorem theorem_3b_value_eq_k (a : List ℕ) (S : Finset (Fin a.length))
    (σ : Schedule a.length) (hS : ∀ j, σ.machine j = 0 ↔ j ∈ S) :
    (σ.IsNonIdle (procB a) → σ.sumWC (procB a) (procB a) = kVal a S) ∧
      (σ.IsFeasible (procB a) → kVal a S ≤ σ.sumWC (procB a) (procB a)) := by sorry

end SchedComplexity.Partition

