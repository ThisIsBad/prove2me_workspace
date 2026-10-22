import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.2 (Balas §5.2.2, p. 75, [13]): the Assignable Subgraph Polytope of a digraph `G`
is defined by the system `0 ≤ x_i ≤ 1`, `x(S \ Γ(S)) − x(Γ(S) \ S) ≤ 0`, `S ⊆ V`. -/
theorem assignable_subgraph_polytope {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop)
    [DecidableRel A] :
    AssignableSubgraphPolytope A =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ S : Finset V, xSum x (S \ GammaOut A S) - xSum x (GammaOut A S \ S) ≤ 0} := by sorry

end Disjunctive.ExtendedFormulations

