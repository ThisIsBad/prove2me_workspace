import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Theorem 5.2, p. 112: the next-node lists created by any complete run of the next-node algorithm
(§5.2, p. 111) on an even, connected graph, started at `r` with an edge `e₀` meeting `r`, satisfy
Theorem 5.1 (i), (ii) and (iii). -/
theorem theorem_5_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V) (e₀ : E)
    (hr : r ∈ G.ends e₀) (L : V → List V) (hL : AlgProduces G r e₀ L) :
    CondI G L ∧ CondII G L ∧ CondIII G r L := by sorry

end ChinesePostman.NextNode

