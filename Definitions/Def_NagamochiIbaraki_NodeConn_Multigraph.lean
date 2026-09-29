import Mathlib

namespace NagamochiIbaraki.NodeConn

/-! Finite graphs (Nagamochi–Ibaraki 1992, p. 583 and §3, p. 589).

A graph `G = (V, E)` is encoded by a node type `V`, an edge type `E` and the map
`ends : E → Sym2 V` sending each edge to its unordered pair of end nodes. Self-loops are
excluded by the hypothesis `∀ e, ¬ (ends e).IsDiag` carried by the theorems, and simplicity
(no two edges with the same pair of end nodes, assumed throughout §3) is
`Function.Injective ends`. An edge subset is a `Finset E`. -/

variable {V E : Type*}

/-- The simple graph on `V` recording which pairs of nodes are joined by at least one edge of
`F`. Adjacency, walks, paths and reachability "in `F`" are those of `edgeGraph ends F`. -/
def edgeGraph (ends : E → Sym2 V) (F : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (ends '' (F : Set E))

end NagamochiIbaraki.NodeConn
