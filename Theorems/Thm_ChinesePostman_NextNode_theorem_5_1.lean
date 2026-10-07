import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Theorem 5.1, p. 112: for any node `r` of an even, connected graph `G`, next-node lists describe
an Euler tour (from `r`) if and only if (i), (ii) and (iii) hold, with (iii) for the edges
`(n, L_n(1))`, `n ≠ r`. -/
theorem theorem_5_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V)
    (L : V → List V) :
    DescribesEulerTour G r L ↔ CondI G L ∧ CondII G L ∧ CondIII G r L := by sorry

end ChinesePostman.NextNode

