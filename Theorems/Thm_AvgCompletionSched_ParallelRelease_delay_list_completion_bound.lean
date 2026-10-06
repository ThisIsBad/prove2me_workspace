import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model
import Definitions.Def_AvgCompletionSched_ParallelRelease_DelayList

namespace AvgCompletionSched.ParallelRelease

/-- Theorem 4.9 without precedence constraints (`κ_i = r_i + p_i`): in a Delay List schedule with
parameter `β > 0` on the list `π`, every job satisfies
`C_i ≤ (1 + β) p(B_i)/m + (1 + 1/β)(r_i + p_i) - p_i/β`, where `B_i` is the set of jobs at or
before `i` in the list. -/
theorem delay_list_completion_bound {n m : ℕ} (I : Instance n m) (hm : 2 ≤ m)
    (π : Fin n ≃ Fin n) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I)
    (hD : IsDelayListSchedule I π β D) (i : Fin n) :
    D.C i ≤ (1 + β) * (∑ k ∈ Finset.univ.filter (fun k => π.symm k ≤ π.symm i), I.p k) / m
      + (1 + 1 / β) * (I.r i + I.p i) - I.p i / β := by sorry

end AvgCompletionSched.ParallelRelease

