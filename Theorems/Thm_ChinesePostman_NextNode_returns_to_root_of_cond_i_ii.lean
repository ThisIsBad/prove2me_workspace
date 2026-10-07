import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113 (converse, first step): under (i) and (ii), the traversal from `r`
specified by the next-node lists ends at `r`, having used every entry of `L r` and every occurrence
of `r` in every list (so every edge meeting `r` has been traversed). -/
theorem returns_to_root_of_cond_i_ii {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (r : V) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) :
    (follow L r).1.getLast? = some r ∧ (follow L r).2 r = (L r).length ∧
      ∀ m, r ∉ unused L (follow L r).2 m := by sorry

end ChinesePostman.NextNode

