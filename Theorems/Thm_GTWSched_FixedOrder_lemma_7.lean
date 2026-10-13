import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- LEMMA 7, p. 338: every algorithmic block is weighted toward Increase,
unless its first task starts at zero. -/
theorem lemma_7 (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n j k : ℕ) (hblock : IsBlock l n (sched a l n) j k) :
    decCount a (sched a l n) j k < incCount a (sched a l n) j k ∨
      sched a l n j = 0 := by sorry

end GTWSched.FixedOrder

