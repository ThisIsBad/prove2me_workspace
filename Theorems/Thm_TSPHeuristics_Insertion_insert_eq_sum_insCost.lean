import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (3.7), p. 571: the length of the tour `T n` built by an insertion method is the sum of the
insertion costs, `INSERT = Σ_{i=1}^{n-1} COST(T_i, a_i)`. -/
theorem insert_eq_sum_insCost {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i) := by sorry

end TSPHeuristics.Insertion
