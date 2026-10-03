import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.247, Eq. (9.15): arcs entering a vertex
subset, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Δ⁻X = {a ∈ A : ∂⁻a ∈ X, ∂⁺a ∈ V∖X}` (Eq. (9.15)), the set of arcs entering `X`, where
`tail = ∂⁺` and `head = ∂⁻`. -/
def DeltaMinus {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (X : Finset V) : Finset A :=
  Finset.univ.filter (fun a => head a ∈ X ∧ tail a ∉ X)

end DiscreteConvex.NetworkFlows
