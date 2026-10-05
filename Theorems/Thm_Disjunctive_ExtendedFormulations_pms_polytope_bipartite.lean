import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.1 (Balas §5.2.1, p. 74, [34]): the PMS polytope of a bipartite graph `G` with
bipartition recorded by `part : V → Bool` is defined by the system (5.5). -/
theorem pms_polytope_bipartite {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (part : V → Bool) (hBip : ∀ i j, G.Adj i j → part i ≠ part j) :
    PMSPolytope G =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        xSum x (Finset.univ.filter (fun i => part i = true)) =
          xSum x (Finset.univ.filter (fun i => part i = false)) ∧
        ∀ S : Finset V, S ⊆ Finset.univ.filter (fun i => part i = true) →
          xSum x S ≤ xSum x (NeighborsF G S)} := by sorry

end Disjunctive.ExtendedFormulations

