import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcs

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: a series arc set, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- A set of arcs is **series** if it consists of pairwise series arcs. -/
def IsSeriesArcSet {V A : Type*} [DecidableEq V] [DecidableEq A] (src dst : A → V)
    (S : Finset A) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsSeriesArcs src dst a b

end DiscreteConvex.CombinatorialC
