import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerToUpper

/-!
The negated total lower capacity of an arc set, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Σ_{a ∈ S} (-c(a))`, the negated total lower capacity of an arc set `S`, landing in
`ℝ ∪ {+∞}` via `NegLowerToUpper`. -/
noncomputable def NegLowerCapOf {A : Type*} (cLower : A → WithBot ℝ) (S : Finset A) : WithTop ℝ :=
  ∑ a ∈ S, NegLowerToUpper (cLower a)

end DiscreteConvex.NetworkFlows
