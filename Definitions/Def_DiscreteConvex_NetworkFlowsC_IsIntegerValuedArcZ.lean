import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def IsIntegerValuedArcZ (g : ℤ → WithTop ℝ) : Prop :=
  ∀ t : ℤ, g t = ⊤ ∨ ∃ n : ℤ, g t = ((n : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsC
