import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(c), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 17): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j` (the proof's standing assumption,
p. 16), KNAPSACK has a solution iff the constructed `n|1|r_n≥0|L_max` instance has a feasible
schedule with `L_max ≤ y = 0`, i.e. `C_j - d_j ≤ 0` for every job. -/
theorem theorem_4c_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ ∀ j, (instCF a b).lateness B j ≤ 0 := by sorry

end SchedComplexity.OneMachine

