import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 8 (first half):
if the 3-dimensional matching instance `T` has a matching, then the scheduling instance of
Theorem 5 built from `T` has a schedule with makespan at most `2`. -/
theorem matching_gives_makespan_two {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : HasMatching T) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by sorry

end UnrelatedSched.ThreeHalves

