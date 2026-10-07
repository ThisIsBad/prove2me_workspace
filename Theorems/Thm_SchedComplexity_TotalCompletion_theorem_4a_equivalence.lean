import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_Knapsack
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Theorem 4(a), the equivalence of the reduction (pp. 22–23): for positive integers
`a_1, …, a_t, b` with `0 < b < A`, KNAPSACK has a solution if and only if the constructed
instance belongs to the class `n|1|r_n≥0,w_j=1|Σw_jC_j` and has a feasible schedule with
`Σ_j C_j ≤ y`. -/
theorem theorem_4a_equivalence {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a) :
    SchedComplexity.Tardiness.KnapsackYes a b ↔
      IsYes (procTime a b) (weight a b) (release a b) (yThreshold a b) := by sorry

end SchedComplexity.TotalCompletion

