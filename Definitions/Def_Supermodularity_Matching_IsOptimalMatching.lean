import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 97, Section 3.2, equation (3.2.1) (the matching problem) and the sentence "A matching that
maximizes the sum of the profits for all the firms is optimal."
-/

namespace Supermodularity.Matching

/-- `IsOptimalMatching f x` says the matching `x : Fin m → ∀ i, X i`, assigning to each of `m`
firms a vector of qualities of `n` worker types, is *optimal* for the profit function `f`: it
maximizes the total profit `∑ j, f (x j) j` over every matching `y : Fin m → ∀ i, X i`. -/
def IsOptimalMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ) (x : Fin m → ∀ i, X i) : Prop :=
  ∀ y : Fin m → ∀ i, X i, ∑ j, f (y j) j ≤ ∑ j, f (x j) j

end Supermodularity.Matching
