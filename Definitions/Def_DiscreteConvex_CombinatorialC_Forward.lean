import Mathlib

/-!
Orientation of an arc relative to a simple-cycle traversal, used for the parallel/series arc
relation (Murota, *Discrete Convex Analysis*, SIAM 2003, p.83), in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Arc `arcs i` is **forward** relative to the cycle traversal `v` if it points from `v i` to
`v (i+1)` (as opposed to the reverse). Meaningful once `{∂⁺(arcs i), ∂⁻(arcs i)} = {v i, v
(i+1)}` holds (`IsSimpleCycle`), in which case exactly one of forward/reverse holds. -/
def Forward {V A : Type*} {k : ℕ} (src : A → V) (v : Fin k → V) (arcs : Fin k → A)
    (i : Fin k) : Prop :=
  src (arcs i) = v i

end DiscreteConvex.CombinatorialC
