import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance

open FlowJobShop.PartitionFlow.FlowShop

namespace FlowJobShop.PartitionFlow

/-- Observations (i)–(ii) in the proof of Lemma 1(b) (Gonzalez–Sahni 1978, p. 39): in every
preemptive schedule of FS with finish time `≤ 2T`, (i) task `t_{1,n+1}` finishes by time `T`
(every piece of it ends by `T`), and (ii) task `t_{3,n+2}` does not start before time `T`
(every piece of it starts at or after `T`). Job `n + 1` is `Sum.inr 0`, job `n + 2` is
`Sum.inr 1`; processors `P_1, P_3` are `0, 2`. -/
theorem observations_i_ii {n : ℕ} (a : Fin n → ℕ) (S : PreemptiveSchedule (FS a))
    (hS : S.finishTime ≤ 2 * T a) :
    (∀ p ∈ S.pieces 0 (Sum.inr 0), p.2 ≤ T a) ∧
      (∀ p ∈ S.pieces 2 (Sum.inr 1), T a ≤ p.1) := by sorry

end FlowJobShop.PartitionFlow

