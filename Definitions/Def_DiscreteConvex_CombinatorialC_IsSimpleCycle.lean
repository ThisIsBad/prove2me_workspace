import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, footnote 33: a simple cycle, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- A **simple cycle** (footnote 33): an alternating sequence of `k+1` vertices
`v : Fin (k+1) → V` (cyclically indexed, `v` injective — the `v_i` are pairwise distinct) and
arcs `arcs : Fin (k+1) → A` such that `{∂⁺(arcs i), ∂⁻(arcs i)} = {v i, v (i+1)}` for every `i`
(`i + 1` wraps cyclically since it is computed in `Fin (k+1)`). Cycle length is `k+1 > 0`. -/
def IsSimpleCycle {V A : Type*} [DecidableEq V] (src dst : A → V) (k : ℕ) (v : Fin (k + 1) → V)
    (arcs : Fin (k + 1) → A) : Prop :=
  Function.Injective v ∧
    ∀ i : Fin (k + 1), ({src (arcs i), dst (arcs i)} : Finset V) = {v i, v (i + 1)}

end DiscreteConvex.CombinatorialC
