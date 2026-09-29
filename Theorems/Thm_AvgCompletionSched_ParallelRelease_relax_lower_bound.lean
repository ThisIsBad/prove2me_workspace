import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 3.1: the optimal value of the one-machine relaxation `I1` is at most the total
completion time of every feasible nonpreemptive `m`-machine schedule of `I`. -/
theorem relax_lower_bound {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (Nstar : Schedule I) :
    ∑ j, P1.CP j ≤ ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
