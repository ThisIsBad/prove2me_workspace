import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Lemma 3.8 (Goldberg–Tarjan 1988, p. 927). The number of relabeling operations is at most
`2n - 1` per vertex and at most `(2n - 1)(n - 2) < 2n²` overall, where `n = |V|`. -/
theorem relabel_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    (∀ v : V, relabelCountAt N σ K v ≤ 2 * Fintype.card V - 1) ∧
      relabelCount N σ K ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
      (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by sorry

end GoldbergTarjan.Generic

