import Mathlib
import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem uniform_pmtn_lower_bound {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (S : PreemptiveSchedule n m) (hS : IsFeasible s p S) :
    levelBound s p ≤ makespan S := by sorry
end SchedulingAlgorithms
