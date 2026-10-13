import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- THEOREM 2, p. 338: the algorithm returns a feasible minimum-cost
schedule among all schedules of the first n tasks in the prescribed order. -/
theorem theorem_2 (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n : ℕ) :
    FixedFeasible l n (sched a l n) ∧
      ∀ s : ℕ → ℝ, FixedFeasible l n s →
        cost a n (sched a l n) ≤ cost a n s := by sorry

end GTWSched.FixedOrder

