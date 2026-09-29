import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- Proof of Theorem 3, p. 15: a graph with `|V| = 3t` has a partition into paths of length 2 if
and only if the constructed instance on two uniform machines with speeds `q_1 = 2`, `q_2 = 1`
has a feasible schedule with `C_max ≤ t`. -/
theorem paths_iff_q2Schedule (d : GraphData) :
    PartitionIntoPathsOfLength2 d.G ↔
      ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)).HasScheduleWithin
        d.t := by sorry

end ResourceScheduling.Graph

