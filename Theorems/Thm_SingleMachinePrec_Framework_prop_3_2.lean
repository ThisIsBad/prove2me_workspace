import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph

namespace SingleMachinePrec.Framework

/-- **Proposition 3.2** (p. 657). For every finite poset `P`, the vertex cover graph `G^S_P` of
`1|prec|∑ w_j C_j` and the graph of incomparable pairs `G_P` coincide. -/
theorem prop_3_2 {N : Type*} [Fintype N] (P : N → N → Prop) [IsPartialOrder N P] :
    vertexCoverGraph P = incPairsGraph P := by sorry

end SingleMachinePrec.Framework

