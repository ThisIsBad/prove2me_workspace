import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The **boundary** `∂ξ(v) = Σ{ξ(a) : a ∈ δ⁺v} − Σ{ξ(a) : a ∈ δ⁻v}` of a real flow, `tail = ∂⁺`,
`head = ∂⁻`. -/
def Boundary (tail head : A → V) (xi : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), xi a)

end DiscreteConvex.NetworkFlowsB
