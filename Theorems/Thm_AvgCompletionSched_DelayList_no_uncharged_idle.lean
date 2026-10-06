import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

open MeasureTheory

/-- Lemma 4.7 (p. 159): for every job `J_i`, once `J_i` has been scheduled and charged there is
no uncharged idle time in the interval `(q^m_i, s^m_i)`, and all the idle time in that interval
is charged only to jobs in `B_i` (no job of `A_i` is charged idle time lying in it). -/
theorem no_uncharged_idle {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i : Fin n) :
    (∫ t in Set.Ioo (D.q i) (D.S i) \ ⋃ k ∈ {k | D.Before k i ∨ k = i}, D.window k,
        D.idle t) = 0 ∧
    ∀ k ∈ listA π i, (∫ t in D.chargedSet k ∩ Set.Ioo (D.q i) (D.S i), D.idle t) = 0 := by sorry

end AvgCompletionSched.DelayList

