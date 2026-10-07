import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- **Lemma 9** (Gonzalez–Sahni 1978, p. 47). In an `m`-processor, `n`-job job shop, the SPT
schedule (the list schedule in any order `σ` of nondecreasing total task time) has mean flow time
at most `m` times that of every feasible non-preemptive schedule `τ`, hence at most `m` times the
optimal mean flow time: `MFT(S) ≤ m · MFT(S*)`, the ratio bound `MFT(S)/MFT(S*) ≤ m` multiplied
out. -/
theorem lemma_9 {m n : ℕ} (inst : Instance m n) (hm : 0 < m)
    (σ : Fin n ≃ Fin n) (hσ : IsSPTOrder inst σ)
    (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    meanFlowTime inst (listSchedule inst σ) ≤ (m : ℝ) * meanFlowTime inst τ := by sorry

end FlowJobShop.SPT

