import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model
import Definitions.Def_AvgCompletionSched_InTree_ListScheduling

namespace AvgCompletionSched.InTree

/-- Theorem 4.17 (p. 162): list scheduling on `m` machines, using an optimal one-machine
schedule as the list, is a 2-approximation for minimizing weighted completion time with in-tree
precedence and no release dates: its value is at most twice that of every feasible `m`-machine
schedule. -/
theorem list_schedule_two_approx {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (N : Schedule I m) :
    G.wct ≤ 2 * N.wct := by sorry

end AvgCompletionSched.InTree

