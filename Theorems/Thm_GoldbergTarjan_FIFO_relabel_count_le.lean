import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 3.8 (Goldberg–Tarjan 1988, p. 927), for the first-in, first-out algorithm: the number of
relabeling operations is at most `2n − 1` per vertex and at most `(2n − 1)(n − 2) < 2n²`
overall, where `n = |V|`. The relabelings counted are the push/relabel operations of all
discharges of the run that take the relabeling branch of Fig. 3. -/
theorem relabel_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    (∀ x, relabelCountAt N L K S J x ≤ 2 * Fintype.card V - 1) ∧
    relabelCount N L K S J ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
    (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by sorry

end GoldbergTarjan.FIFO

