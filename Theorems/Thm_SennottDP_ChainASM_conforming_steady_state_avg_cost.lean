import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem conforming_steady_state_avg_cost {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (AS : ApproxSeq Γ)
    (hconf : AS.IsConforming z) :
    (∀ i : S, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i))) ∧
    ∃ Jc : ℕ → ℝ≥0∞, (∀ᶠ N in atTop, ∀ i ∈ AS.SN N, AS.avgCostN N i = Jc N) ∧
      Tendsto Jc atTop (𝓝 (Γ.classAvgCost (Γ.commClass z))) := by sorry

end SennottDP.ChainASM

