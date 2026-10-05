import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem upper_hessenberg_excess_to_N_conforming
    (Γ : MC ℕ) (hz : Γ.IsZStandard 0)
    (hHess : ∀ i j : ℕ, 2 ≤ i → j + 1 < i → Γ.P i j = 0)
    (AS : ApproxSeq Γ) (hN₀ : 1 ≤ AS.N₀)
    (hSN : ∀ N, AS.N₀ ≤ N → AS.SN N = Finset.range (N + 1))
    (q : ℕ → ℕ → ℕ → ℕ → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N → q N i r N = 1) :
    AS.IsConforming 0 := by sorry

end SennottDP.ChainASM

