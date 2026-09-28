import Mathlib
open scoped Pointwise

namespace Erdos52
end Erdos52

open Erdos52

theorem solution (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by
  have h := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hA
  rw [two_mul]
  exact h
