import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model

namespace BurnInBatch.AgreeTmax

/-- Justification of Algorithm DP2 (p. 770, by reference to that of DP1, p. 768): with jobs
indexed so that due dates and processing times are both nondecreasing, if the jobs `1, …, j`
(`j ≤ n`) can be scheduled with `T_max = 0`, then among such schedules one of minimum makespan
is a consecutive partition: its batches are sets of consecutively indexed jobs, in increasing
order of index. -/
theorem consecutive_optimal {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n)
    (hfeas : ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0) :
    ∃ S : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0 ∧
      IsConsecutive S ∧
      ∀ S' : List (Finset (Fin n)), IsValid B (jobsUpTo n j) S' → Tmax p d S' = 0 →
        makespan p S ≤ makespan p S' := by sorry

end BurnInBatch.AgreeTmax

