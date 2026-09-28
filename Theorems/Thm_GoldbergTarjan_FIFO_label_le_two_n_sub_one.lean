import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 3.7 (Goldberg–Tarjan 1988, p. 927), for the first-in, first-out algorithm: at any time
during the execution of the algorithm and for any vertex `v ∈ V`, `d(v) ≤ 2n − 1`, where
`n = |V|`. "At any time" covers the states between discharges and the configurations between
the push/relabel operations inside each discharge. -/
theorem label_le_two_n_sub_one {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    (∀ k ≤ K, ∀ v, (S k).cfg.d v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)) ∧
    (∀ k < K, ∀ j ≤ J k, ∀ v,
      (prIter N L (frontVertex N (S k)) (S k).cfg j).d v
        ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)) := by sorry

end GoldbergTarjan.FIFO

