import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Lemma 1(b) (Gonzalez–Sahni 1978, p. 39): if `S = {a_1, …, a_n}` has no partition, then every
preemptive schedule of the flow shop FS built from it has finish time `> 2T`. -/
theorem lemma_1b {n : ℕ} (a : Fin n → ℕ) (h : ¬ HasPartition a) :
    ∀ S : PreemptiveSchedule (FS a), 2 * T a < S.finishTime := by sorry

end FlowJobShop.PartitionFlow

