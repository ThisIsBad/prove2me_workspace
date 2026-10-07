import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(f), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 17): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the
constructed `n|1|r_n≥0,w_j=1|∑w_jU_j` instance (the construction of (c), unit weights) has a
feasible schedule with `∑ w_j U_j ≤ y = 0`. -/
theorem theorem_4f_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0 := by sorry

end SchedComplexity.OneMachine

