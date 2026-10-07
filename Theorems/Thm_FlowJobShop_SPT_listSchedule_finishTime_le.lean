import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- In the list schedule that processes the jobs in the order `σ`, the job in position `k`
finishes no later than the total task time of the jobs in positions `0, …, k`:
`f_{σ k}(S) ≤ ∑_{j ≤ k} L_{σ j}` (Gonzalez–Sahni 1978, proof of Lemma 9, p. 47). -/
theorem listSchedule_finishTime_le {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n)
    (k : Fin n) :
    finishTime inst (listSchedule inst σ) (σ k) ≤
      ∑ j ∈ Finset.Iic k, inst.jobLength (σ j) := by sorry

end FlowJobShop.SPT

