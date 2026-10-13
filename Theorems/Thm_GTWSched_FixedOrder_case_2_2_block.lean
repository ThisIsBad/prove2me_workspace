import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- Case 2.2 of THEOREM 2, p. 338: an alternative that places the new task
earlier moves every task of R's final block earlier and cannot lower that
block's total discrepancy. -/
theorem case_2_2_block (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) (n : ℕ) (hn : 0 < n)
    (hlate : a n < sched a l n (n - 1) + l (n - 1))
    (s : ℕ → ℝ) (hs : FixedFeasible l (n + 1) s) :
    let r := place (sched a l n) n (sched a l n (n - 1) + l (n - 1))
    let j := blockStart l r n
    s n < r n →
      (∀ i, j ≤ i → i ≤ n → s i ≤ r i) ∧
      (∑ i ∈ Finset.Icc j n, |r i - a i|) ≤
        ∑ i ∈ Finset.Icc j n, |s i - a i| := by sorry

end GTWSched.FixedOrder

