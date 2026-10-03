import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.74, Eq. (2.27): the boundary (net outflow) of
a flow, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The boundary `∂ξ(v) = ∑_{a: ∂⁺a=v} ξ(a) − ∑_{a: ∂⁻a=v} ξ(a)` (Eq. (2.27)): the net flow
leaving vertex `v`, given the initial-vertex map `src` and terminal-vertex map `dst`. -/
noncomputable def Boundary {V A : Type*} [Fintype A] (src dst : A → V) [DecidableEq V]
    (xi : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => src a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => dst a = v), xi a)

end DiscreteConvex.CombinatorialC
