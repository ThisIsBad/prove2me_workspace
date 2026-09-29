import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- The balanced bound (p. 164): if moreover `∑ p_j > α ∑ C*_j`, then
`∑ C^D_j ≤ (2 + β + (1 - α)/β) ∑ C*_j`. -/
theorem delay_list_balanced_bound {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (P1 : RelaxSchedule I) (hP1 : P1.IsOptimal) (π : Fin n ≃ Fin n)
    (hπ : IsCompletionOrder P1 π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (Nstar : Schedule I) (α : ℝ)
    (hα : α * ∑ j, Nstar.C j < ∑ j, I.p j) :
    ∑ j, D.C j ≤ (2 + β + (1 - α) / β) * ∑ j, Nstar.C j := by sorry

end AvgCompletionSched.ParallelRelease
