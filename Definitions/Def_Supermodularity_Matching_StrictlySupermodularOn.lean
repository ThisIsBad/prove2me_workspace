import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 44, Section 2.6.1 (definition of a strictly supermodular function).
-/

namespace Supermodularity.Matching

/-- `StrictlySupermodularOn f S` says the real-valued function `f` on a lattice `X` is
*strictly* supermodular on `S ⊆ X`: `f x + f y < f (x ⊔ y) + f (x ⊓ y)` for every pair of
*unordered* (incomparable) `x y ∈ S`. Taking `S = Set.univ` recovers Topkis's plain "`f` is
strictly supermodular on `X`". -/
def StrictlySupermodularOn {X : Type*} [Lattice X] (f : X → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S → ¬ x ≤ y → ¬ y ≤ x →
    f x + f y < f (x ⊔ y) + f (x ⊓ y)

end Supermodularity.Matching
