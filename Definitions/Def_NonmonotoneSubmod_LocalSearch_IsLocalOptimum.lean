import Mathlib

namespace NonmonotoneSubmod.LocalSearch

/-- Local optimum (Feige–Mirrokni–Vondrák 2011, §3.1, p. 1140): `S` is a local optimum of `f` if
neither including a new element in `S` nor discarding one of the elements of `S` increases the
value of `S`, i.e. `f (S ∪ {a}) ≤ f S` for every `a ∉ S` and `f (S \ {a}) ≤ f S` for every
`a ∈ S`. -/
def IsLocalOptimum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (S : Finset X) :
    Prop :=
  (∀ a, a ∉ S → f (insert a S) ≤ f S) ∧ (∀ a, a ∈ S → f (S.erase a) ≤ f S)

end NonmonotoneSubmod.LocalSearch
