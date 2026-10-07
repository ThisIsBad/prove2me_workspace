import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- Theorem 2(d), the equivalence (p. 14): for a directed graph `G'` on `Fin n` and a chosen
vertex `v'`, `G'` has a Hamilton circuit iff the graph `G` obtained by keeping the arcs of `G'`
that do not enter `v'` and redirecting the arcs entering `v'` to a new vertex `v''` has a
Hamilton path. -/
theorem theorem_2d_equiv {n : ℕ} (adj' : Fin n → Fin n → Bool) (v' : Fin n) :
    HasHamiltonCircuit adj' ↔ HasHamiltonPath (hcToHpGraph adj' v') := by sorry

end SchedComplexity.NoWait

