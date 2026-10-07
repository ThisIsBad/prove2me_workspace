import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Theorem 1 (Gonzalez–Sahni 1978, p. 38), in the form its proof establishes: for every
PARTITION instance `S = {a_1, …, a_n}`, the three-processor flow shop FS built from it has at
most two nonzero tasks per job, and it has a preemptive schedule with finish time `≤ 2T` iff
`S` has a partition, and a non-preemptive schedule with finish time `≤ 2T` iff `S` has a
partition. -/
theorem theorem_1 {n : ℕ} (a : Fin n → ℕ) :
    (FS a).AtMostTwoNonzeroTasks ∧
      ((∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a) ∧
      ((∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
        HasPartition a) := by sorry

end FlowJobShop.PartitionFlow

