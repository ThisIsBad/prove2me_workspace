import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem atas_structural_conforming {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q) (Nstar : ℕ)
    (h37 : ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * Γ.meanPassage {z} j ≤ Γ.meanPassage {z} r)
    (h38 : ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * Γ.passageCost {z} j ≤ Γ.passageCost {z} r) :
    AS.IsConforming z := by sorry

end SennottDP.ChainASM

