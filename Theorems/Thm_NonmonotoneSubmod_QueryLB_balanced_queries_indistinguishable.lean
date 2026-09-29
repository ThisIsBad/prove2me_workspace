import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (p. 1150, first paragraph): if every query that a deterministic
`q`-query algorithm `A` issues against the cut oracle `g(S) = |S|(n − |S|)` is balanced for
`(C, Cᶜ)`, then `A` receives the same answers from `f_C` as from `g`, issues the same queries
and returns the same set. -/
theorem balanced_queries_indistinguishable (n m q : ℕ) (A : DetAlg (Fin n) q)
    (C : Finset (Fin n)) (hbal : ∀ i < q, Balanced n m C (A.queryAt (gCut n) i)) :
    (∀ i ≤ q, A.answers (fC n m C) i = A.answers (gCut n) i) ∧
      A.run (fC n m C) = A.run (gCut n) := by sorry

end NonmonotoneSubmod.QueryLB
