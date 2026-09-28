import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.10 (Goldberg–Tarjan 1988, p. 928). Under the standing assumption `m ≥ n - 1`
(§2, p. 923), the number of nonsaturating pushing operations is at most `4n²m`, where
`n = |V|` and `m = |E|`. -/
theorem nonsaturating_push_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hm : Fintype.card V - 1 ≤ N.numEdges)
    (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    nonsaturatingPushCount N σ K ≤ 4 * Fintype.card V ^ 2 * N.numEdges := by sorry

end GoldbergTarjan.Generic

