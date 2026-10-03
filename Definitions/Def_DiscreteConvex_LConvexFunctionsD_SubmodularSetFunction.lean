import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set function `ρ : 2^V → R∪{+∞}` is submodular, with `ρ(∅)=0` and `ρ(V) < +∞` (the class
`S[R]`). -/
def SubmodularSetFunction (rho : Finset V → WithTop ℝ) : Prop :=
  rho ∅ = 0 ∧ rho Finset.univ ≠ ⊤ ∧
    ∀ X Y : Finset V, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y)

end DiscreteConvex.LConvexFunctionsD
