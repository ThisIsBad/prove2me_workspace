import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.247, Eq. (9.14): arcs leaving a vertex subset,
in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Δ⁺X = {a ∈ A : ∂⁺a ∈ X, ∂⁻a ∈ V∖X}` (Eq. (9.14)), the set of arcs leaving `X`, where
`tail = ∂⁺` and `head = ∂⁻`. -/
def DeltaPlus {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (X : Finset V) : Finset A :=
  Finset.univ.filter (fun a => tail a ∈ X ∧ head a ∉ X)

end DiscreteConvex.NetworkFlows
