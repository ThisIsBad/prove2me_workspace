import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm

namespace AvgCompletionSched.DelayList

/-- Theorem 4.13 (p. 161): given an instance `I` of scheduling with release dates and precedence
constraints to minimize the sum of weighted completion times, and a feasible one-machine schedule
`S^1` of `I` within a factor `ρ` of every feasible one-machine schedule of `I`, every run of the
continuous-time algorithm Delay List (`β > 0`, `m ≥ 2` machines) using `S^1` as the list gives an
`m`-machine schedule whose sum of weighted completion times is within a factor
`(1 + β) ρ + (1 + 1/β)` of that of every feasible `m`-machine schedule of `I`. -/
theorem delay_list_approximation {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (β ρ : ℝ)
    (hβ : 0 < β) (S1 : Schedule I 1) (hρ : ∀ S1' : Schedule I 1, S1.wct ≤ ρ * S1'.wct)
    (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder S1 π) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (N : Schedule I m) :
    D.wct ≤ ((1 + β) * ρ + (1 + 1 / β)) * N.wct := by sorry

end AvgCompletionSched.DelayList

