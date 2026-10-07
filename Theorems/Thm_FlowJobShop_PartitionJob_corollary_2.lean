import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Corollary 2 (Gonzalez–Sahni 1978, p. 44), in the form its proof establishes: the job shop
`JS(a)` has a non-preemptive schedule with finish time `≤ 5T` iff `a` has a partition. -/
theorem corollary_2 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a := by sorry

end FlowJobShop.PartitionJob

