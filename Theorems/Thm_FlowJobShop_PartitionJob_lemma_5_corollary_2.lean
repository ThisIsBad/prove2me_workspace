import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionJob_Schedule
import Definitions.Def_FlowJobShop_PartitionJob_JS

namespace FlowJobShop.PartitionJob

open JobShopLTAS.Core

/-- Lemma 5 and Corollary 2 (Gonzalez–Sahni 1978, pp. 43–44): for every PARTITION instance `a`,
the two-processor job shop `JS(a)` (`n` jobs with two tasks, two jobs with three tasks) has a
preemptive schedule with finish time `≤ 5T` iff `a` has a partition, and has a non-preemptive
schedule with finish time `≤ 5T` iff `a` has a partition. -/
theorem lemma_5_corollary_2 {n : ℕ} (a : Fin n → ℕ) :
    ((∃ S : Schedule (JS a), S.IsPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a) ∧
    ((∃ S : Schedule (JS a), S.IsNonPreemptive ∧ S.FinishedBy (5 * FlowJobShop.PartitionFlow.T a)) ↔ FlowJobShop.PartitionFlow.HasPartition a) := by sorry

end FlowJobShop.PartitionJob

