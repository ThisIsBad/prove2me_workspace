import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- §5, proof of Theorem 7, p. 9 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987)): "for each
matching there is a schedule with makespan pq". If the family `S` of `q`-subsets of the ground set
`Fin (q * n)` has a matching `F'`, the scheduling instance `twoTimes p q n S` has a schedule whose
makespan is at most `p * q`. -/
theorem matching_gives_schedule (p q : ℕ) {m n : ℕ} (S : Fin m → Finset (Fin (q * n)))
    (hS : ∀ i, (S i).card = q) (F' : Finset (Fin m)) (hF' : IsQMatching S F') :
    ∃ σ : Fin (q * n + p * (m - n)) → Fin m,
      makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ) := by sorry

end UnrelatedSched.TwoTimes

