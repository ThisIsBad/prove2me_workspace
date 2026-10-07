import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Makespan

/-- p. 403, node counts of the branch-and-bound run with the bound `LB` of p. 401, for
`n ≥ 1` jobs:
(a) whenever the first node of the list is terminal, at least `½ n (n+1)` nodes have been
created;
(b) at every stage at most `1 + n + n(n-1) + ⋯ + n!/1! = ∑_{k<n} n!/(n-k)!` nodes have been
created;
(c) at every stage the list holds at most `n!` nodes. -/
theorem node_counts {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      n * (n + 1) ≤ 2 * createdCount (lowerBound a b c) k) ∧
    (∀ k, createdCount (lowerBound a b c) k ≤ ∑ j ∈ Finset.range n, n.descFactorial j) ∧
    (∀ k, (run (lowerBound a b c) k).length ≤ n.factorial) := by sorry

end IgnallSchrage.Makespan

