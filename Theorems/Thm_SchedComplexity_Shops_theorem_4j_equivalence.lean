import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(j), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 17: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the three-machine job
shop `constrJ a b` (items with order `(M_1, M_3)` and times `a_j, a_j`; `J_{n-1}` with order
`(M_1, M_2)` and times `b, 2(A - b)`; `J_n` with order `(M_2, M_3)` and times `2b, A - b`) has a
feasible schedule with `C_max ≤ y = 2A`. -/
theorem theorem_4j_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrJ a b).HasScheduleLE (yJ a) := by sorry

end SchedComplexity.Shops

