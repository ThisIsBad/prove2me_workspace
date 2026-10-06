import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[R]): submodularity of a polyhedral convex function. -/
def SBFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.ConjugacyDualityB
