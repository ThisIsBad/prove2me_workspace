import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(i), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 16: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the two-machine job shop
`constrI a b` (items on `M_1` with `p_j1 = a_j`; `J_n` with machine order `(M_2, M_1, M_2)` and
times `b, 1, A - b`) has a feasible schedule with `C_max ≤ y = A + 1`. -/
theorem theorem_4i_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrI a b).HasScheduleLE (yI a) := by sorry

end SchedComplexity.Shops

