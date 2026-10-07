import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Proof of Lemma 7(b), p. 45: if the schedule ends by `2tB`, every
piece of operation `i` of the long job lies in its allotted interval
`[iB,(i+1)B]`. Total work and disjointness ensure the interval is filled. -/
theorem forced_long_job (C : ThreePartition) (hvalid : C.Valid)
    (S : PreemptiveSchedule (reductionInstance C))
    (hfinish : S.FinishesBy (threshold C)) :
    ∀ u : Fin S.pieceCount, (S.op u).1.val = 3 * C.t →
      ((S.op u).2.val : ℝ) * C.b ≤ S.start u ∧
        S.finish u ≤ (((S.op u).2.val + 1 : ℕ) : ℝ) * C.b := by sorry

end FlowJobShop.ThreePartJob

