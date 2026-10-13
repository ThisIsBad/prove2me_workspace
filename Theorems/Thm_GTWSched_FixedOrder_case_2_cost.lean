import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- Case 2 of THEOREM 2, p. 338: inserting the late new task adds precisely
its discrepancy; a subsequent balanced-block shift costs nothing. -/
theorem case_2_cost (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n : ℕ) (hn : 0 < n)
    (hlate : a n < sched a l n (n - 1) + l (n - 1)) :
    cost a (n + 1) (sched a l (n + 1)) =
      cost a n (sched a l n) +
        (sched a l n (n - 1) + l (n - 1) - a n) := by sorry

end GTWSched.FixedOrder

