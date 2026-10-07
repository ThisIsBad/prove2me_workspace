import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7, p. 44: the constructed two-machine job shop admits a
preemptive schedule of finish time at most `2tB` exactly when the input
has a 3-partition. -/
theorem lemma_7_preemptive (C : ThreePartition) (hvalid : C.Valid) :
    (∃ S : PreemptiveSchedule (reductionInstance C),
      S.FinishesBy (threshold C)) ↔ C.HasSolution := by sorry

end FlowJobShop.ThreePartJob

