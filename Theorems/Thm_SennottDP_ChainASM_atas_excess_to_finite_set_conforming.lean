import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem atas_excess_to_finite_set_conforming {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (G : Finset S) (hG : G.Nonempty)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : AS.SendsExcessTo q (↑G : Set S)) :
    AS.IsConforming z ∧
      ((↑G : Set S) ⊆ Γ.commClass z → AS.IsConformingOn (Γ.commClass z)) := by sorry

end SennottDP.ChainASM

