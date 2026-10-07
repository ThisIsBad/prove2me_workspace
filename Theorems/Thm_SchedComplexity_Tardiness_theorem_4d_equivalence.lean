import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Definitions.Def_SchedComplexity_Tardiness_Knapsack

namespace SchedComplexity.Tardiness

/-- The equivalence of Theorem 4(d), p. 20: for positive `a_1, …, a_t`, `0 < b < A` and every
`τ > 2t' + A`, KNAPSACK has a solution iff the constructed instance of `n|1||Σw_jT_j` has a
feasible schedule (arbitrary start times in `ℕ`, idle time allowed) with `Σ w_j T_j ≤ y`. -/
theorem theorem_4d_equivalence {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ) :
    KnapsackYes a b ↔ HasScheduleLE (wtP a b τ) (wtW a b τ) (wtD a b τ) (yThr a b τ) := by sorry

end SchedComplexity.Tardiness

