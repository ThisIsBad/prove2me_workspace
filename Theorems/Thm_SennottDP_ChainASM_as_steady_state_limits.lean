import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_steady_state_limits {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) :
    (∀ i : S, ¬ Γ.PosRecurrent i →
      Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i)) ∧
        Γ.steadyState i = 0) ∧
    (∀ R : Set S, Γ.IsPosRecClass R → ∀ Nr : ℕ → ℕ, StrictMono Nr →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b : ℝ≥0∞, b ≤ 1 ∧
        ∀ i ∈ R, Tendsto (fun s => AS.steadyStateN (Nr (φ s)) i) atTop
          (𝓝 (b * Γ.steadyState i))) := by sorry

end SennottDP.ChainASM

