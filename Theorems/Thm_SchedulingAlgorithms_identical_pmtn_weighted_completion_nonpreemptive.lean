import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem identical_pmtn_weighted_completion_nonpreemptive {n m : ℕ} (hm : 0 < m)
    (p w : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hw : ∀ i, 0 ≤ w i) :
    ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧ Nonpreemptive S ∧
      ∀ S' : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S' →
        totalWeightedCompletionOf w S ≤ totalWeightedCompletionOf w S' := by sorry
end SchedulingAlgorithms
