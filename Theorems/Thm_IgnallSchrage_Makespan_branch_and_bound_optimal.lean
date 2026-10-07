import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Makespan

/-- p. 402, stopping rule, with the bound of p. 401: for `n ≥ 1` jobs and any real processing
times, (i) the branch-and-bound run reaches a list whose first node is terminal, and (ii)
whenever the first node `P` of the list is terminal, `P` is the beginning of a full sequence
`σ*` (namely `P` followed by its one unscheduled job) whose makespan is at most the makespan of
every one of the `n!` sequences. -/
theorem branch_and_bound_optimal {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∃ k P, (run (lowerBound a b c) k).head? = some P ∧ IsTerminal P) ∧
    ∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      ∃ σstar : Equiv.Perm (Fin n), BeginsWith σstar P ∧
        ∀ σ : Equiv.Perm (Fin n), makespan a b c σstar ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan

