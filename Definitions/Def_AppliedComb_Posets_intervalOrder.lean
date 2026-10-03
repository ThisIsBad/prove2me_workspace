import Mathlib

namespace AppliedComb.Posets

/-- Interval order (Keller & Trotter, p. 128): there is an assignment `x ↦ [a x, b x]` of
closed real intervals (degenerate intervals `a x = b x` allowed) such that for all `x y`,
`x < y` in the poset if and only if `b x < a y` in `ℝ`. -/
def IsIntervalOrder (α : Type*) [PartialOrder α] : Prop :=
  ∃ a b : α → ℝ, (∀ x, a x ≤ b x) ∧ ∀ x y : α, x < y ↔ b x < a y

/-- The poset `2 + 2` (Keller & Trotter, pp. 128–129): the disjoint sum of two copies of the
2-element chain `2 = {0, 1}`. Mathlib's order on `Fin 2 ⊕ Fin 2` is the disjoint-sum order
(`Sum.LiftRel`): `z ≤ w` iff both lie in the same summand and `z ≤ w` there. -/
abbrev TwoPlusTwo : Type := Fin 2 ⊕ Fin 2

/-- `P` excludes `Q` (Keller & Trotter, p. 119): no subposet of `P` is isomorphic to `Q`,
i.e. there is no order embedding of `Q` into `P`. -/
def Excludes (α β : Type*) [PartialOrder α] [PartialOrder β] : Prop :=
  IsEmpty (β ↪o α)

end AppliedComb.Posets
