import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set function `ρ : 2^V → Z` is submodular, with `ρ(∅) = 0` — the standing normalization of
Murota, *Discrete Convex Analysis*, SIAM 2003, §10.2.1 (p. 285), on which Propositions 10.8,
10.9 (3), 10.20 and 10.23 all depend (with `V = {v}`, `ρ(∅) = -1`, `ρ({v}) = 0` the base
polyhedron is empty and the min-max relation of 10.8 is false). -/
def Submodular (rho : Finset V → ℤ) : Prop :=
  rho ∅ = 0 ∧ ∀ X Y : Finset V, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y)

end DiscreteConvex.AlgorithmsB
