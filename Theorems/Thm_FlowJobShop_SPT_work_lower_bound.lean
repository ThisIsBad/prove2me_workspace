import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime

open JobShopLTAS.Core

namespace FlowJobShop.SPT

/-- Let `τ` be any feasible non-preemptive schedule of an `m`-processor job shop, and let
`ρ 0, ρ 1, …` be the order in which the jobs finish in `τ` (finish times nondecreasing).
Then for every `k`, `m · f_{ρ k}(τ) ≥ ∑_{j ≤ k} L_{ρ j}` (Gonzalez–Sahni 1978, proof of Lemma 9,
p. 47: `f_{i_k}(S*) ≥ ∑_{j=1}^k L_{i_j}/m`, multiplied by `m`). -/
theorem work_lower_bound {m n : ℕ} (inst : Instance m n) (hm : 0 < m) (τ : inst.Op → ℝ)
    (hτ : IsPaperFeasibleSchedule inst τ) (ρ : Fin n ≃ Fin n)
    (hρ : Monotone fun k => finishTime inst τ (ρ k)) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, inst.jobLength (ρ j) ≤ (m : ℝ) * finishTime inst τ (ρ k) := by sorry

end FlowJobShop.SPT

