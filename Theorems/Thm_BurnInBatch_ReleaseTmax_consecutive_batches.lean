import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- Justification of DP1 (§3, p. 768): with the jobs indexed in nondecreasing order of due dates
and of release times, every on-time batch schedule `S` of the first `j` jobs can be replaced by
an on-time batch schedule `S'` of the same jobs whose batches are blocks of consecutively indexed
jobs (at most `B` each, as in every batch schedule), in increasing index order, with makespan no
larger than that of `S`. -/
theorem consecutive_batches {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hd : Monotone d) (hr : Monotone r) (j : ℕ) (hj : j ≤ n)
    (S : List (Finset (Fin n))) (hS : IsBatchSchedule B (prefixJobs n j) S)
    (hon : AllOnTime p r d (prefixJobs n j) S) :
    ∃ S' : List (Finset (Fin n)),
      IsBatchSchedule B (prefixJobs n j) S' ∧ AllOnTime p r d (prefixJobs n j) S' ∧
      IsConsecutive S' ∧ makespan p r S' ≤ makespan p r S := by sorry

end BurnInBatch.ReleaseTmax

