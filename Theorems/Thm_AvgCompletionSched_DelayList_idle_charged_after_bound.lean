import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

/-- Lemma 4.8 (pp. 159–160): for every job `J_i` and every path `P′_i` of Definition 4.4, the
total idle time charged to jobs in `A_i`, in the interval `(0, s^m_i)`, is at most
`m (κ′_i − p_i)`; consequently `p(O_i) ≤ m (κ′_i − p_i)/β ≤ m (κ_i − p_i)/β`. -/
theorem idle_charged_after_bound {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    D.chargedToIn (listA π i) (Set.Ioo 0 (D.S i)) ≤ (m : ℝ) * (kappaPrime I j₁ l - I.p i) ∧
    psum I (D.outOfOrder π i) ≤ (m : ℝ) * (kappaPrime I j₁ l - I.p i) / β ∧
    (m : ℝ) * (kappaPrime I j₁ l - I.p i) / β ≤ (m : ℝ) * (kappa I i - I.p i) / β := by sorry

end AvgCompletionSched.DelayList

