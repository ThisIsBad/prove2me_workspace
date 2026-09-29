import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

/-- Fact 4.5 (p. 159): `κ′_i ≤ κ_i`, for every path `P′_i` of Definition 4.4 in a Delay List
schedule. -/
theorem kappa_prime_le_kappa {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    kappaPrime I j₁ l ≤ kappa I i := by sorry

end AvgCompletionSched.DelayList
