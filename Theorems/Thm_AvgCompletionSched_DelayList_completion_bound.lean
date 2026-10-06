import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

/-- Theorem 4.9 (p. 160): let `S^m` be a schedule produced by the continuous-time algorithm Delay
List using a list `π` that obeys the precedence constraints. Then for each job `J_i` and every
path `P′_i` of Definition 4.4,
`C^m_i ≤ (1 + β) p(B_i)/m + (1 + 1/β) κ′_i − p_i/β`. -/
theorem completion_bound {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    D.C i ≤ (1 + β) * psum I (listB π i) / m + (1 + 1 / β) * kappaPrime I j₁ l
      - I.p i / β := by sorry

end AvgCompletionSched.DelayList

