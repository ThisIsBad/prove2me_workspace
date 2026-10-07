import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7(b), p. 45: without a 3-partition, every preemptive
schedule of the constructed job shop finishes strictly after `2tB`. -/
theorem lemma_7b (C : ThreePartition) (hvalid : C.Valid) (hno : ¬ C.HasSolution) :
    ∀ S : PreemptiveSchedule (reductionInstance C),
      ∃ u : Fin S.pieceCount, threshold C < S.finish u := by sorry

end FlowJobShop.ThreePartJob

