import Mathlib

namespace Supermodularity.Lattices

/-- The induced (Veinott/strong) set ordering `⊑` on subsets of a lattice `X`:
`InducedSetOrder A B` says `A ⊑ B`. -/
def InducedSetOrder {X : Type*} [Lattice X] (A B : Set X) : Prop :=
  ∀ ⦃a : X⦄, a ∈ A → ∀ ⦃b : X⦄, b ∈ B → a ⊓ b ∈ A ∧ a ⊔ b ∈ B

end Supermodularity.Lattices
