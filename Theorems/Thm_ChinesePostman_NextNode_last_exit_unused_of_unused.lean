import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113 (converse, second step): under (i) and (ii), when the traversal
from `r` stops, every node `n` incident to an untraversed edge (an unused entry of `L n`, or an
unused occurrence of `n` in some list `L m`) is different from `r`, and its last exit `L_n(1)` is
still unused. -/
theorem last_exit_unused_of_unused {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (r : V) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) (n : V)
    (hn : unused L (follow L r).2 n ≠ [] ∨ ∃ m, n ∈ unused L (follow L r).2 m) :
    n ≠ r ∧ ∃ m, (L n).head? = some m ∧ (unused L (follow L r).2 n).head? = some m := by sorry

end ChinesePostman.NextNode

