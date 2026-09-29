import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 3.2: list scheduling in the order of completion times of an optimal preemptive schedule
of `I1` is a `(3 - 1/m)`-approximation for total completion time. -/
theorem list_schedule_approx {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (Nstar : Schedule I) :
    ∑ j, listCompletion I π j ≤ (3 - (1 : ℝ) / m) * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
