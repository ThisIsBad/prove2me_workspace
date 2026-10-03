import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSimpleCycle
import Definitions.Def_DiscreteConvex_CombinatorialC_Forward

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83: series arcs, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Two arcs are **series**: every simple cycle containing both of them orients them in the
same direction. -/
def IsSeriesArcs {V A : Type*} [DecidableEq V] (src dst : A → V) (a b : A) : Prop :=
  ∀ k (v : Fin (k + 1) → V) (arcs : Fin (k + 1) → A), IsSimpleCycle src dst k v arcs →
    ∀ i j : Fin (k + 1), arcs i = a → arcs j = b →
      (Forward src v arcs i ↔ Forward src v arcs j)

end DiscreteConvex.CombinatorialC
