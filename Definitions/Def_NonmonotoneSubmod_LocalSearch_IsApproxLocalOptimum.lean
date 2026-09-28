import Mathlib

namespace NonmonotoneSubmod.LocalSearch

/-- Definition 3.2 (Feige–Mirrokni–Vondrák 2011, p. 1141): a set `S` is a `(1 + α)`-approximate
local optimum of `f` if `(1 + α) f(S) ≥ f(S \ {v})` for every `v ∈ S` and
`(1 + α) f(S) ≥ f(S ∪ {v})` for every `v ∉ S`. -/
def IsApproxLocalOptimum {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (α : ℝ)
    (S : Finset X) : Prop :=
  (∀ v, v ∈ S → f (S.erase v) ≤ (1 + α) * f S) ∧
    (∀ v, v ∉ S → f (insert v S) ≤ (1 + α) * f S)

end NonmonotoneSubmod.LocalSearch
