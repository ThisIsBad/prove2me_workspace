import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Corollary 1 (Gonzalez–Sahni 1978, pp. 39–40), in the form its proof establishes: the flow
shop FS of Lemma 1 has a non-preemptive schedule with finish time `≤ τ = 2T` iff
`S = {a_1, …, a_n}` has a partition. -/
theorem corollary_1 {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
      HasPartition a := by sorry

end FlowJobShop.PartitionFlow

