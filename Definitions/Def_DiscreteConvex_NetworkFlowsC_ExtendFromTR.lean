import Mathlib

namespace DiscreteConvex.NetworkFlowsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vector of `Rⱽ` extending `y ∈ Rᵀ` by zero outside `T`; the real-domain counterpart of
`ExtendFromT`. -/
def ExtendFromTR (T : Finset V) (y : {v // v ∈ T} → ℝ) : V → ℝ :=
  fun v => if h : v ∈ T then y ⟨v, h⟩ else 0

end DiscreteConvex.NetworkFlowsC
