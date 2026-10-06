import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- Lemma 4.18: Delay List with parameter `β > 0` applied to the list of an optimal preemptive
schedule `P1` of `I1` gives `∑ C^D_j ≤ (2 + β) ∑ C*_j + (1/β) ∑ r_j`. -/
theorem delay_list_relax_bound {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (P1 : RelaxSchedule I) (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (Nstar : Schedule I) :
    ∑ j, D.C j ≤ (2 + β) * ∑ j, Nstar.C j + 1 / β * ∑ j, I.r j := by sorry

end AvgCompletionSched.ParallelRelease

