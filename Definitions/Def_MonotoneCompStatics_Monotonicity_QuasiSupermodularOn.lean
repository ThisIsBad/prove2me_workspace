import Mathlib

namespace MonotoneCompStatics.Monotonicity

def QuasiSupermodularOn {X : Type*} [Lattice X] (g : X → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S →
    (g (x ⊓ y) ≤ g x → g y ≤ g (x ⊔ y)) ∧ (g (x ⊓ y) < g x → g y < g (x ⊔ y))

end MonotoneCompStatics.Monotonicity
