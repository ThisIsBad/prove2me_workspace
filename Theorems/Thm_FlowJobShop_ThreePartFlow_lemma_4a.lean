import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_FlowJobShop_ThreePartFlow_Instance

open ResourceScheduling.Chain
open FlowJobShop.ThreePartFlow.FlowShop

namespace FlowJobShop.ThreePartFlow

/-- Lemma 4(a) (Gonzalez–Sahni 1978, proof of Lemma 4, p. 41): if the 3-Partition instance
`C = (a_1, …, a_s, B)`, `s = 3t`, `t ≥ 2`, has a solution, then the flow shop `FS` built from
it has a non-preemptive schedule with finish time `≤ 2tB`. -/
theorem lemma_4a (C : ThreePartition) (hC : C.Valid) (ht : 2 ≤ C.t) (hsol : C.HasSolution) :
    ∃ S : PreemptiveSchedule (FS C), S.IsNonPreemptive ∧ S.finishTime ≤ tau C := by sorry

end FlowJobShop.ThreePartFlow

