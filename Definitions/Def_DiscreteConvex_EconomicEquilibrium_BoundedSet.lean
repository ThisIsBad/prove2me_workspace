import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325 (the boundedness assumption on `dom Cl`,
carried throughout chapter 11, e.g. Proposition 11.10, p.335, and pp.331-332's "bounded nonempty
effective domain"): boundedness of a subset of the integer lattice `Zᴷ`, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- A set `S ⊆ Zᴷ` is bounded: there is a single integer bound `N` with `|x(k)| ≤ N` for every
`x ∈ S` and `k ∈ K`. -/
def BoundedSet {K : Type*} (S : Set (K → ℤ)) : Prop :=
  ∃ N : ℤ, ∀ x ∈ S, ∀ k : K, |x k| ≤ N

end DiscreteConvex.EconomicEquilibrium
