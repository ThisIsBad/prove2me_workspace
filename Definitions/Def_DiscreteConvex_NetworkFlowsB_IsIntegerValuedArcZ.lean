import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate function `g : Z → R ∪ {+∞}` is integer valued. -/
def IsIntegerValuedArcZ (g : ℤ → WithTop ℝ) : Prop :=
  ∀ t : ℤ, g t = ⊤ ∨ ∃ n : ℤ, g t = ((n : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB
