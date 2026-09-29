import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §II, pp. 1391–1392 (P1 and P2: an isolated terminal or fragment "can be
connected"; "an N-terminal network is connected by N-1 applications"): in a connected labelled
graph, a construction by P1 and P2 with fewer than `N - 1` links can always be extended by one
more application of P1 or P2. This is the "can be connected" of the principles made explicit.
Implicit hypothesis made explicit: `G` is connected. -/
theorem construction_extends {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : IsConstruction G w l) (hlen : l.length < Fintype.card V - 1) :
    ∃ e : Sym2 V, IsConstruction G w (l ++ [e]) := by sorry

end ShortestConnection.Principles
