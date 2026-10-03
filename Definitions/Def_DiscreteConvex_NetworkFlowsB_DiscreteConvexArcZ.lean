import Mathlib

namespace DiscreteConvex.NetworkFlowsB

/-- A univariate arc cost `ψ : Z → R∪{+∞}` is discrete convex (the book's class `C[Z→R]`).
Theorem 9.16 assumes each `fa` lies in it; without the assumption the potential criterion fails
(one arc, `f` the indicator of `0`, `fa(t) = -t²`: the zero flow is optimal but no potential puts
`0` in `arg min (fa + δp)`). -/
def DiscreteConvexArcZ (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.NetworkFlowsB
