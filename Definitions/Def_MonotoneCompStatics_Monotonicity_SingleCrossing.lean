import Mathlib

namespace MonotoneCompStatics.Monotonicity

def SingleCrossing {X T : Type*} [PartialOrder X] [PartialOrder T] (f : X → T → ℝ) : Prop :=
  ∀ ⦃x' x'' : X⦄, x'' < x' → ∀ ⦃t' t'' : T⦄, t'' < t' →
    (f x'' t'' < f x' t'' → f x'' t' < f x' t') ∧
    (f x'' t'' ≤ f x' t'' → f x'' t' ≤ f x' t')

end MonotoneCompStatics.Monotonicity
