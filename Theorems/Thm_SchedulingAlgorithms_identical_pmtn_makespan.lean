import Mathlib
import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem identical_pmtn_makespan {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) :
    (∀ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S →
        mcNaughtonBound hn p m ≤ makespan S) ∧
      ∃ S : PreemptiveSchedule n m, IsFeasible (fun _ => 1) p S ∧
        makespan S = mcNaughtonBound hn p m := by sorry
end SchedulingAlgorithms
