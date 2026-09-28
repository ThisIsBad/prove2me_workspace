import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 96-97, Section 3.2 (definition of an increasing matching).
-/

namespace Supermodularity.Matching

/-- `IsIncreasingMatching x` says the matching `x : Fin m → ∀ i, X i`, which assigns to each
of `m` firms a vector of qualities of `n` worker types (one worker of each type), is
*increasing*: `x 1 ⪯ x 2 ⪯ ⋯ ⪯ x m`, i.e. `x` is monotone in the firm index `j`, with respect
to the pointwise (product) order on `∀ i, X i`. -/
def IsIncreasingMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (x : Fin m → ∀ i, X i) : Prop :=
  Monotone x

end Supermodularity.Matching
