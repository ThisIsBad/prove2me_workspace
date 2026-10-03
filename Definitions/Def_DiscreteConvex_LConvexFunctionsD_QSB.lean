import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QSB): `g` is quasi submodular. -/
def QSB (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g (p ⊓ q) ≤ g p ∨ g (p ⊔ q) ≤ g q

end DiscreteConvex.LConvexFunctionsD
