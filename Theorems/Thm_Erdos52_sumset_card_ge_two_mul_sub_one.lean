import Mathlib
open scoped Pointwise

namespace Erdos52
theorem sumset_card_ge_two_mul_sub_one (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by sorry
end Erdos52
