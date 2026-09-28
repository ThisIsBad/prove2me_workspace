import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Theorem 3.11 with Theorem 3.4 (Goldberg–Tarjan 1988, pp. 928 and 926). Under the standing
assumption `m ≥ n - 1` (p. 923), every execution of the generic push-relabel algorithm (started
with the simple labeling, basic operations applied in any order) performs at most
`(2n - 1)(n - 2) + 2nm + 4n²m` basic operations — `O(n²m)` in the paper, explicit from
Lemmas 3.8–3.10 — and, if no basic operation applies at its end, the final preflow is a
maximum flow. -/
theorem generic_push_relabel_correct_and_bounded {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hm : Fintype.card V - 1 ≤ N.numEdges)
    (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    K ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) +
        2 * Fintype.card V * N.numEdges + 4 * Fintype.card V ^ 2 * N.numEdges ∧
      (NoBasicOpApplicable N (σ K) → IsMaxFlow N (σ K).1) := by sorry

end GoldbergTarjan.Generic

