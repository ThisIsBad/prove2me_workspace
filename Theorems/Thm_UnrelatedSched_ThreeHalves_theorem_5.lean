import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, Theorem 5, p. 7 (the reduction its
proof establishes): the scheduling instance built from the 3-dimensional matching instance `T`
has a schedule with makespan at most `2` if and only if `T` has a matching. -/
theorem theorem_5 {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2) ↔
      HasMatching T := by sorry

end UnrelatedSched.ThreeHalves

