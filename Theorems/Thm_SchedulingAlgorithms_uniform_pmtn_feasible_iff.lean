import Definitions.Def_SchedulingAlgorithms_ParallelMachines

namespace SchedulingAlgorithms
theorem uniform_pmtn_feasible_iff {n m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (hs : ∀ j, 0 < s j) (hs' : Antitone s)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hp' : Antitone p)
    (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : PreemptiveSchedule n m, IsFeasible s p S ∧ makespan S ≤ T) ↔
      ∀ A : Finset (Fin n), ∑ i ∈ A, p i ≤ T * speedCapacity s A := by sorry
end SchedulingAlgorithms
