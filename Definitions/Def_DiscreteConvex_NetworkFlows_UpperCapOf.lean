import Mathlib

/-!
The total upper capacity of an arc set, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Σ_{a ∈ S} c̄(a)`, the total upper capacity of an arc set `S`. -/
noncomputable def UpperCapOf {A : Type*} (cUpper : A → WithTop ℝ) (S : Finset A) : WithTop ℝ :=
  ∑ a ∈ S, cUpper a

end DiscreteConvex.NetworkFlows
