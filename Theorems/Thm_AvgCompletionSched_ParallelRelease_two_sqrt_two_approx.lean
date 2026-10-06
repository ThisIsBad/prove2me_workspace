import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 4.19 (with the constant `2√2 ≈ 2.8284 < 2.83` of its proof): let `P1` be an optimal
preemptive schedule of the one-machine relaxation, `π` the list of jobs in order of completion in
`P1`, `N` the strict-order list schedule of `π`, and `D` a Delay List schedule on `π` with
`β = √(3 - 2√2)`. Then the better of `N` and `D` has total completion time at most `2√2` times
that of every feasible nonpreemptive schedule. -/
theorem two_sqrt_two_approx {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder P1 π)
    (D : DelayListRun I) (hD : IsDelayListSchedule I π (Real.sqrt (3 - 2 * Real.sqrt 2)) D)
    (Nstar : Schedule I) :
    min (∑ j, listCompletion I π j) (∑ j, D.C j) ≤ 2 * Real.sqrt 2 * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease

