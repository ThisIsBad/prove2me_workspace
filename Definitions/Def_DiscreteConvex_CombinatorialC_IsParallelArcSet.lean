import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsParallelArcs

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: a parallel arc set, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- A set of arcs is **parallel** if it consists of pairwise parallel arcs. -/
def IsParallelArcSet {V A : Type*} [DecidableEq V] [DecidableEq A] (src dst : A → V)
    (P : Finset A) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a ≠ b → IsParallelArcs src dst a b

end DiscreteConvex.CombinatorialC
