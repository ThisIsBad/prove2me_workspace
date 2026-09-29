import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic
import Definitions.Def_LubyMIS_Derandomized_AlgorithmD

namespace LubyMIS.Derandomized

/-- Case 1 is rare (Luby 1986, §4.4, p. 1046): in every run of Algorithm D, Case 1 occurs in at most
16 executions of the loop body. Only the executions before termination are counted (`V′` nonempty at
every index up to `k`): after the first index with `V′ = ∅` a run is unconstrained. -/
theorem case1_at_most_16 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (s : ℕ → Finset (Fin n) × Finset (Fin n))
    (hs : IsRun G q s) (K : ℕ) :
    ((Finset.range K).filter
      (fun k => (∀ j ≤ k, (s j).2.Nonempty) ∧ Case1 G (s k))).card ≤ 16 := by sorry

end LubyMIS.Derandomized
