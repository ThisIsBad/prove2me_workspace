import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph

namespace NagamochiIbaraki.EdgeConn

variable {V E : Type*}

/-- The local edge-connectivity `λ(x, y; (V, F))` of the nodes `x, y` in the spanning subgraph
`(V, F)` of a multigraph: the minimum number of edges `W ⊆ F` whose removal leaves no path
between `x` and `y` in `(V, F \ W)`. Parallel edges are counted separately. The value lies in
`ℕ∞`; it is `⊤` exactly when `x = y` (no edge set separates a node from itself), and `0` when
`x` and `y` are already disconnected in `(V, F)`. -/
noncomputable def localEdgeConn [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (x y : V) : ℕ∞ :=
  ⨅ W ∈ {W : Finset E | W ⊆ F ∧ ¬ (edgeGraph ends (F \ W)).Reachable x y}, (W.card : ℕ∞)

end NagamochiIbaraki.EdgeConn
