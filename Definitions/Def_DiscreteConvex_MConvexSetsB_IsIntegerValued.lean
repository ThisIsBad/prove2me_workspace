import Mathlib

/-!
Integer-valuedness of an `R ∪ {+∞}`-valued set function (the book's `ρ ∈ S[Z]`), used
throughout this mission (Murota, *Discrete Convex Analysis*, SIAM 2003, pp.107-116), in
`DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- `ρ : 2ⱽ → R ∪ {+∞}` is **integer valued** (the book's `ρ ∈ S[Z]`, as opposed to `S[R]`) if
every finite value it takes is (the cast of) an integer. -/
def IsIntegerValued {V : Type*} (ρ : Finset V → WithTop ℝ) : Prop :=
  ∀ X : Finset V, ρ X = ⊤ ∨ ∃ k : ℤ, ρ X = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexSetsB
