import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 97, Section 3.2 (definition of an ordered matching).
-/

namespace Supermodularity.Matching

/-- `IsOrderedMatching x` says the matching `x : Fin m → ∀ i, X i` is *ordered*: the quality
vectors `x j'` and `x j''` assigned to any two firms `j'` and `j''` are comparable in the
pointwise (product) order on `∀ i, X i`. Every increasing matching is ordered, but an ordered
matching need not be increasing (the `m` vectors are only pairwise comparable, not one total
chain from firm `1` to firm `m`). -/
def IsOrderedMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (x : Fin m → ∀ i, X i) : Prop :=
  ∀ j k : Fin m, x j ≤ x k ∨ x k ≤ x j

end Supermodularity.Matching
