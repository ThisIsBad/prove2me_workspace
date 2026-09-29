import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- (3.3): for any preemptive schedule `P1` of `I1` and any list `π` ordering the jobs by their
completion times in `P1`, the strict-order list schedule `N` satisfies
`∑ C^N_j ≤ 2 ∑ C^{P1}_j + (1 - 1/m) ∑ p_j`. -/
theorem list_schedule_sum_bound {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π) :
    ∑ j, listCompletion I π j ≤
      2 * ∑ j, P1.CP j + (1 - (1 : ℝ) / m) * ∑ j, I.p j := by sorry

end AvgCompletionSched.ParallelRelease
