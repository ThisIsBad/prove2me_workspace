import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.9 (Goldberg–Tarjan 1988, p. 927). The number of saturating push operations is at
most `2nm`, where `n = |V|` and `m = |E|`. -/
theorem saturating_push_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    saturatingPushCount N σ K ≤ 2 * Fintype.card V * N.numEdges := by sorry

end GoldbergTarjan.Generic

