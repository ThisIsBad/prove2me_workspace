import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Lemma 1(a) (Gonzalez–Sahni 1978, p. 39): if `S = {a_1, …, a_n}` has a partition, then the
flow shop FS built from it has a non-preemptive schedule with finish time `2T`. -/
theorem lemma_1a {n : ℕ} (a : Fin n → ℕ) (h : HasPartition a) :
    ∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime = 2 * T a := by sorry

end FlowJobShop.PartitionFlow

