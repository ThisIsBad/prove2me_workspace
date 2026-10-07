import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Lemma 1 (Gonzalez–Sahni 1978, p. 38; proof p. 39), in the form its proof establishes: the
three-processor flow shop FS built from `S = {a_1, …, a_n}` has a preemptive schedule with
finish time `≤ 2T` iff `S` has a partition. -/
theorem lemma_1 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a := by sorry

end FlowJobShop.PartitionFlow

