import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- For every feasible non-preemptive schedule `τ` of an `m`-processor, `n`-job job shop and every
SPT order `σ`, `m · MFT(τ) ≥ (1/n) ∑_{k} ∑_{j ≤ k} L_{σ j}` (Gonzalez–Sahni 1978, proof of
Lemma 9, p. 47: `MFT(S*) ≥ (1/n) ∑_{k=1}^n ∑_{j=1}^k L_j/m`, multiplied by `m`). -/
theorem mft_lower_bound {m n : ℕ} (inst : Instance m n) (hm : 0 < m) (σ : Fin n ≃ Fin n)
    (hσ : IsSPTOrder inst σ) (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) / n ≤
      (m : ℝ) * meanFlowTime inst τ := by sorry

end FlowJobShop.SPT

