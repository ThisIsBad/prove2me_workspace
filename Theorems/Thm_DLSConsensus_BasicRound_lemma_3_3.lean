import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Lemma 3.3 (p. 297): immediately after any lock-release phase `k` (round `4k`) that occurs at
or after GST, the set of values locked by processors in `C` has at most one element. -/
theorem lemma_3_3 {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (C : Finset (Fin N)) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (k : ℕ) (hk : 1 ≤ k) (hGST : GST ≤ 4 * k) :
    {v : V | ∃ p ∈ C, (exec t pick init deliv (4 * k) p).lock v ≠ none}.Subsingleton := by sorry

end DLSConsensus.BasicRound

