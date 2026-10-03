import Mathlib

/-!
Integer-valuedness of a `ℝ ∪ {+∞}`-valued function, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A `ℝ ∪ {+∞}`-valued function is **integer valued** if every finite value it takes is an
integer. -/
def IsIntegerUpper {α : Type*} (g : α → WithTop ℝ) : Prop :=
  ∀ a : α, ∀ r : ℝ, g a = (r : WithTop ℝ) → ∃ n : ℤ, (n : ℝ) = r

end DiscreteConvex.NetworkFlows
