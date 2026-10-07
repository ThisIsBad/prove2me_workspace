import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, pp. 112–113: if next-node lists describe an Euler tour, then they
satisfy (i) and (ii). -/
theorem cond_i_ii_of_describes {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (r : V) (L : V → List V)
    (h : DescribesEulerTour G r L) :
    CondI G L ∧ CondII G L := by sorry

end ChinesePostman.NextNode

