import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(b), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 19): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the
constructed `n|1|L_max≤0|∑w_jC_j` instance has a feasible schedule meeting every due date
(`C_j ≤ d_j` for all `j`) with `∑ w_j C_j ≤ y = ∑_{j,k∈T, j≤k} a_j a_k + A - b`. -/
theorem theorem_4b_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
        (instB a b).sumWC B ≤ yB a b := by sorry

end SchedComplexity.OneMachine

