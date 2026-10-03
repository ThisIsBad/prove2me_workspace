import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.245, Eq. (9.1): the boundary of a flow, in
`DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- The **boundary** `∂ξ(v) = Σ{ξ(a) : a ∈ δ⁺v} - Σ{ξ(a) : a ∈ δ⁻v}` (Eq. (9.1)) of a flow
`ξ : A → ℝ` on a digraph with vertex set `V`, arc set `A`, and tail/head maps `tail = ∂⁺`,
`head = ∂⁻ : A → V`. -/
noncomputable def Boundary {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (ξ : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), ξ a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), ξ a)

end DiscreteConvex.NetworkFlows
