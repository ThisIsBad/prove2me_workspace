import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_Shops_Constructions

namespace SchedComplexity.Shops

/-- Theorem 4(h), Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 18: for positive integers
`a_1, …, a_t`, `b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the two-machine flow shop
`constrH a b` (items with `p_j1 = t a_j`, `p_j2 = 1`; `J_{n-1}` with `p = (1, t b)`; `J_n` with
`p = (1, t(A - b))`; precedence `J_{n-1} < J_n`) has a feasible schedule with
`C_max ≤ y = t(A + 1) + 1`. -/
theorem theorem_4h_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    SchedComplexity.OneMachine.KnapsackYes a b ↔ (constrH a b).HasScheduleLE (yH a) := by sorry

end SchedComplexity.Shops

