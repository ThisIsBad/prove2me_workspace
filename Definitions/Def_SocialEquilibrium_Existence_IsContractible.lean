import Mathlib

namespace SocialEquilibrium.Existence

open unitInterval

/-- Debreu (1952), §1, p. 888: a set `Z` is *deformable into the point* `z₀ ∈ Z` if there is a
continuous map (a *deformation*) `H : I × Z → Z`, `I = [0, 1]`, with `H(0, z) = z` and
`H(1, z) = z₀` for all `z ∈ Z`. -/
def IsDeformableInto {Y : Type*} [TopologicalSpace Y] (Z : Set Y) (z₀ : Z) : Prop :=
  ∃ H : C(I × Z, Z), (∀ z : Z, H (0, z) = z) ∧ ∀ z : Z, H (1, z) = z₀

/-- Debreu (1952), §1, p. 888: a nonempty set `Z` is *contractible* if it is deformable into
some point `z₀ ∈ Z`. Nonemptiness is carried by the point `z₀ ∈ Z`. -/
def IsContractible {Y : Type*} [TopologicalSpace Y] (Z : Set Y) : Prop :=
  ∃ z₀ : Z, IsDeformableInto Z z₀

end SocialEquilibrium.Existence
