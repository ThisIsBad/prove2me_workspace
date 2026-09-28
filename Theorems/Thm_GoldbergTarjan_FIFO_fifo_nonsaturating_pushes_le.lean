import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Corollary 4.4 (Goldberg–Tarjan 1988, p. 931): the number of nonsaturating pushes during the
first-in, first-out algorithm is at most `4n³`, where `n = |V|`. Stated for every network,
every edge list order, every initial queue order and every run of `K` discharge operations
(Fig. 4) from the initialization of Fig. 2 with the simple labeling. -/
theorem fifo_nonsaturating_pushes_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    nonsatPushCount N L K S J ≤ 4 * Fintype.card V ^ 3 := by sorry

end GoldbergTarjan.FIFO

