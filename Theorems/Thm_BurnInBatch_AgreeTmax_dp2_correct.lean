import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_AgreeTmax_DP2

namespace BurnInBatch.AgreeTmax

/-- Correctness of Algorithm DP2 (Lee, Uzsoy & Martin-Vega 1992, §3, p. 770): with jobs indexed
so that due dates and processing times are both nondecreasing, for every prefix length `j ≤ n`,
`dp2 B p d j` is the minimum makespan over all valid batch schedules of the jobs `1, …, j` with
`T_max = 0`, and `⊤` (the infimum of the empty set in `ℕ∞`) if there is none. -/
theorem dp2_correct {n B : ℕ} (hB : 0 < B) (p d : Fin n → ℕ)
    (hd : Monotone d) (hp : Monotone p) (j : ℕ) (hj : j ≤ n) :
    dp2 B p d j =
      ⨅ (S : List (Finset (Fin n))) (_ : IsValid B (jobsUpTo n j) S ∧ Tmax p d S = 0),
        (makespan p S : ℕ∞) := by sorry

end BurnInBatch.AgreeTmax

