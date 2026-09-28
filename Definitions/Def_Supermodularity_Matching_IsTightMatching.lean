import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 96, Section 3.2 (the labor market is tight if there are exactly `m` workers of each type,
so a feasible matching partitions that fixed supply among the `m` firms).
-/

namespace Supermodularity.Matching

/-- `IsTightMatching x` says the matching `x : Fin m → ∀ i, X i` is feasible in a *tight*
labor market, in which the supply of each worker type `i` is exactly the `m` elements of
`X i` (one per firm, no worker left unhired and no worker hired twice): for each type `i`,
the map `j ↦ x j i` sending firms to the quality of the type-`i` worker they hire is a
bijection onto `X i`. -/
def IsTightMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (x : Fin m → ∀ i, X i) : Prop :=
  ∀ i, Function.Bijective (fun j : Fin m => x j i)

end Supermodularity.Matching
