import Mathlib

/-!
Submodularity of a `ℝ ∪ {+∞}`-valued set function, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A set function `g : 2^V → ℝ ∪ {+∞}` is **submodular** if
`g(X) + g(Y) ≥ g(X ∪ Y) + g(X ∩ Y)` for all `X, Y ⊆ V`. -/
def Submodular {V : Type*} [DecidableEq V] (g : Finset V → WithTop ℝ) : Prop :=
  ∀ X Y : Finset V, g X + g Y ≥ g (X ∪ Y) + g (X ∩ Y)

end DiscreteConvex.NetworkFlows
