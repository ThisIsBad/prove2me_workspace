import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem4Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- Theorem 4 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), p. 7), in the form its proof
establishes: for the scheduling instance `thm4Times T` built from a 3-DIMENSIONAL MATCHING
instance `T` (`m` machines, `3n` element jobs, `m - n` dummy jobs, all processing times in
`{1, 3}`), there is a schedule with makespan at most `3` if and only if `T` has a matching.
"NP-complete" is not formalized. -/
theorem theorem_4 {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (3 * n + (m - n)) → Fin m,
        makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ 3) ↔
      ∃ F' : Finset (Fin m), IsThreeDimMatching T F' := by sorry

end UnrelatedSched.TwoTimes

