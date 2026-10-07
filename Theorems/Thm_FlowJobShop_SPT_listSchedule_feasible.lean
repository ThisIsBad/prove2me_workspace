import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- The list schedule that processes the jobs in the order `σ` is a feasible non-preemptive
schedule of all jobs: starts are nonnegative, the tasks of a job are processed in order, and two
positive-time tasks on the same processor do not overlap. -/
theorem listSchedule_feasible {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n) :
    IsPaperFeasibleSchedule inst (listSchedule inst σ) := by sorry

end FlowJobShop.SPT

