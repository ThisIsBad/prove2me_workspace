import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- Proof of Theorem 2, p. 15: a graph with `|V| = 3t` has a partition into triangles if and
only if the constructed instance on three identical machines has a feasible schedule with
`C_max ≤ t`. -/
theorem triangles_iff_p3Schedule (d : GraphData) :
    PartitionIntoTriangles d.G ↔
      ((reduce d).toInstance 3 (fun _ => 1) (fun _ => one_pos)).HasScheduleWithin d.t := by sorry

end ResourceScheduling.Graph

