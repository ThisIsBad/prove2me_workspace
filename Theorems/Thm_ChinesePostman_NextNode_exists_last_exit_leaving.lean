import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113 (necessity of (iii)): if next-node lists describe an Euler tour of
a connected graph, then every node `n ≠ r` has a last exit `L_n(1)`, and every nonempty set `S` of
nodes not containing `r` has a node `n ∈ S` whose last exit `L_n(1)` lies outside `S`. -/
theorem exists_last_exit_leaving {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (hconn : Connected G) (r : V) (L : V → List V)
    (h : DescribesEulerTour G r L) :
    (∀ n, n ≠ r → L n ≠ []) ∧
      ∀ S : Finset V, S.Nonempty → r ∉ S →
        ∃ n ∈ S, ∃ m, (L n).head? = some m ∧ m ∉ S := by sorry

end ChinesePostman.NextNode

