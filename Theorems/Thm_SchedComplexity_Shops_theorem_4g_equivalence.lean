import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(g), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 18: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the two-machine flow shop
`constrG a b` (items with `r_j = 0`, `p_j1 = t a_j`, `p_j2 = 1`; `J_n` with `r_n = t b`,
`p_n1 = 1`, `p_n2 = t(A - b)`) has a feasible schedule with `C_max ≤ y = t(A + 1)`. -/
theorem theorem_4g_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrG a b).HasScheduleLE (yG a) := by sorry

end SchedComplexity.Shops

