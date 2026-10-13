import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is supermodular. -/
def SupermodularPair (f : (Fin 2 → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : Fin 2 → ℝ, f p + f q ≤ f (p ⊔ q) + f (p ⊓ q)

end DiscreteConvex.ConjugacyDualityB
