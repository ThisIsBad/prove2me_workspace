import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible

namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared

/-- §6 (p. 80): with the jobs numbered by deadline (`d` monotone) and penalties `p j ≥ 0`, the
problem of §5 is equivalent to the prefix-constrained knapsack problem: every sequence is matched
by a feasible `x` with `∑ p_j - ∑ p_j x_j` at most its weighted number of tardy jobs, and every
feasible `x` is matched by a sequence whose weighted number of tardy jobs is at most
`∑ p_j - ∑ p_j x_j`. -/
theorem equivalent_prefix_knapsack {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    (∀ l : List (Fin n), IsSchedule Finset.univ l →
      ∃ x : Fin n → Bool, PrefixFeasible a' d x ∧
        (∑ j, p j) - knapValue p x ≤ weightedTardy a' d p l) ∧
    (∀ x : Fin n → Bool, PrefixFeasible a' d x →
      ∃ l : List (Fin n), IsSchedule Finset.univ l ∧
        weightedTardy a' d p l ≤ (∑ j, p j) - knapValue p x) := by sorry

end LawlerMoore.WeightedTardy

