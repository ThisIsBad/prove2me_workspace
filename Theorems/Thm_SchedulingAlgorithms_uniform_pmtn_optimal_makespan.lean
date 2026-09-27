import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem uniform_pmtn_optimal_makespan {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p) :
    ∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S = levelBound s p ∧
      ∀ S' : PreemptiveSchedule n m, IsFeasible s p S' → makespan S ≤ makespan S' := by sorry
end SchedulingAlgorithms
