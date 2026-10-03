import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, citing Eq. (3.68), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- A univariate function `ψ : Z → R ∪ {+∞}` is **discrete convex** (the book's `ψ ∈ C[Z→R]`):
nonempty effective domain and the discrete midpoint-convexity inequality
`ψ(x)+ψ(x+2) ≥ 2ψ(x+1)`. -/
def DiscreteConvexUnivariate (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.MConvexFunctionsB
