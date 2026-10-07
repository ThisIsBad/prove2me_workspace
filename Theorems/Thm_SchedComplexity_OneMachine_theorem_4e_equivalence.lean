import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(e), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 19): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the
constructed `n|1||∑w_jU_j` instance (`p_{j1} = w_j = a_j`, `d_j = b`) has a feasible schedule
with `∑ w_j U_j ≤ y = A - b`. -/
theorem theorem_4e_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b := by sorry

end SchedComplexity.OneMachine

