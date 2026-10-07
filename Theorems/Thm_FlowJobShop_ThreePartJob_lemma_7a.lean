import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Instance
import Definitions.Def_FlowJobShop_ThreePartJob_Schedules

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- Lemma 7(a), pp. 44–45: a 3-partition produces a nonpreemptive
schedule of the constructed job shop within `2tB`. -/
theorem lemma_7a (C : ThreePartition) (hvalid : C.Valid) (hsol : C.HasSolution) :
    ∃ s : (reductionInstance C).Op → ℝ,
      NonpreemptiveFinishesBy (reductionInstance C) s (threshold C) := by sorry

end FlowJobShop.ThreePartJob

