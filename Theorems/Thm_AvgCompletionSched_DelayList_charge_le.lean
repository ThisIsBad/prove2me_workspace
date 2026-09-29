import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm

namespace AvgCompletionSched.DelayList

/-- Fact 4.6 (p. 159): in the continuous-time Delay List algorithm, the idle time charged to each
job `J_i` is at most `β p_i`. -/
theorem charge_le {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    D.charge i ≤ β * I.p i := by sorry

end AvgCompletionSched.DelayList
