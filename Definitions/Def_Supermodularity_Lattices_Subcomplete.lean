import Mathlib

namespace Supermodularity.Lattices

/-- `Subcomplete S` says the subset `S` of a lattice `X` is a subcomplete sublattice
of `X`: `S` is a sublattice, and every nonempty subset of `S` has a supremum and an
infimum in `X` that both lie in `S`. -/
def Subcomplete {X : Type*} [Lattice X] (S : Set X) : Prop :=
  IsSublattice S ∧
    ∀ ⦃U : Set X⦄, U ⊆ S → U.Nonempty →
      (∃ s : X, IsLUB U s ∧ s ∈ S) ∧ (∃ i : X, IsGLB U i ∧ i ∈ S)

end Supermodularity.Lattices
