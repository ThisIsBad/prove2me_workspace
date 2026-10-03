import Mathlib

namespace DiscreteConvex.NetworkFlowsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vector of `Zⱽ` extending `y ∈ Zᵀ` by zero outside `T`. The induced functions `f̃` and `g̃`
of Eqs. (9.81) and (9.82) are the book's functions **on `Zᵀ`**; read on all of `Zⱽ` they are
cylinders along `V ∖ T`, and the exchange axiom then fails whenever `T ≠ V` (comparing `y` with
`y + χw` for `w ∉ T` leaves the negative support empty). -/
def ExtendFromT (T : Finset V) (y : {v // v ∈ T} → ℤ) : V → ℤ :=
  fun v => if h : v ∈ T then y ⟨v, h⟩ else 0

end DiscreteConvex.NetworkFlowsC
