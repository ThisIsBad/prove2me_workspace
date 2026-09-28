import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model
import Definitions.Def_AvgCompletionSched_InTree_ListScheduling

namespace AvgCompletionSched.InTree

/-- Lemma 4.16 (p. 162): if `G` is the list schedule on `m` machines using a one-machine
schedule `S¹` (the idle-free schedule in the order `π`) as the list, then for every job `i`,
`C^m_i ≤ κ_i + C^1_i / m`. -/
theorem list_schedule_completion_bound {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : ObeysPrecedence I π) (G : Schedule I m)
    (hG : IsListSchedule I π G) (i : Fin n) :
    G.C i ≤ kappa I i + oneMachineC I π i / (m : ℝ) := by sorry

end AvgCompletionSched.InTree

