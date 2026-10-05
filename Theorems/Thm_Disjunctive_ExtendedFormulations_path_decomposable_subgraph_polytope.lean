import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.3 (Balas §5.2.3, p. 75-76, [13]): the `s`-`t` Path Decomposable Subgraph Polytope
of an acyclic digraph `(V,A)` is defined by the system `0 ≤ x_i ≤ 1`, `x(S \ Γ*(S)) − x(Γ*(S) \
S) ≤ 0`, `S ⊆ V \ {s,t}`. The polytope's points are incidence vectors of subsets of `V \ {s,t}`,
so both sides fix `x_s = x_t = 0`; without that the unit vector `e_s` satisfies the system and is
not in the polytope. Acyclicity is the page's own hypothesis on the digraph. -/
theorem path_decomposable_subgraph_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) [DecidableRel A] (s t : V) (hst : s ≠ t)
    (hacyclic : IsAcyclicDigraph A) :
    PathDecomposableSubgraphPolytope A s t =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x s = 0 ∧ x t = 0 ∧
        ∀ S : Finset V, s ∉ S → t ∉ S →
          xSum x (S \ GammaStar A s t S) - xSum x (GammaStar A s t S \ S) ≤ 0} := by sorry

end Disjunctive.ExtendedFormulations

