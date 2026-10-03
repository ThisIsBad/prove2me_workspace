import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The coboundary `δp(a) = p(∂⁺a) − p(∂⁻a)` of a potential `p : V → R`. -/
def Coboundary (tail head : A → V) (p : V → ℝ) (a : A) : ℝ := p (tail a) - p (head a)

end DiscreteConvex.NetworkFlowsB
