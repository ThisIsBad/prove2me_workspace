import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model
import Definitions.Def_BurnInBatch_ReleaseTmax_DP1

namespace BurnInBatch.ReleaseTmax

/-- Correctness of Algorithm DP1 (§3, p. 768). One batch machine of capacity `B ≥ 1`, `n` jobs
with common processing time `p`, release times `r` and due dates `d`, indexed so that both `d`
and `r` are nondecreasing. For every prefix length `j ≤ n`, the DP1 value `f(j)` equals the
minimum makespan over all batch schedules of jobs `1, …, j` in which every job is on time, and
it is `⊤ = ∞` exactly when there is no such schedule (an infimum over the empty set in `ℕ∞`). -/
theorem dp1_correct {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (hB : 0 < B)
    (hd : Monotone d) (hr : Monotone r) (j : ℕ) (hj : j ≤ n) :
    dp1 B p r d j =
      ⨅ (S : List (Finset (Fin n)))
        (_ : IsBatchSchedule B (prefixJobs n j) S ∧ AllOnTime p r d (prefixJobs n j) S),
        (makespan p r S : ℕ∞) := by sorry

end BurnInBatch.ReleaseTmax

