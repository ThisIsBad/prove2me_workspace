import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (3.10), p. 572: in an insertion method run, for `j < i < n` (so `a_j` already lies in
`T_i` when `a_i` is inserted), `COST(T_i, a_i) ≤ 2 · d(a_i, a_j)`. -/
theorem insCost_le_two_mul_dist_of_lt {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i j : ℕ, j < i → i < n → insCost d (T i) (a i) ≤ 2 * d (a i) (a j) := by sorry

end TSPHeuristics.Insertion
