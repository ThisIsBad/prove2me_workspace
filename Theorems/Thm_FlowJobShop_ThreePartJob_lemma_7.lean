import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7, p. 44, with the nonpreemptive form established by its
part (a) and the inclusion of nonpreemptive schedules among preemptive
ones. The mathematical content is the reduction equivalence. -/
theorem lemma_7 (C : ThreePartition) (hvalid : C.Valid) :
    ((∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution) ∧
    ((∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C)) ↔
        C.HasSolution) := by sorry

end FlowJobShop.ThreePartJob

