import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §II, p. 1392 ("an N-terminal network is connected by N-1 applications"): the
links of a complete construction by P1 and P2 (one with `N - 1` links, `N = card V`) form a
spanning subtree of the labelled graph `G`.
Implicit hypothesis made explicit: `G` is connected (in particular `V` is nonempty, so
`card V - 1` is ordinary subtraction). -/
theorem complete_construction_isSpanningSubtree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : IsCompleteConstruction G w l) :
    IsSpanningSubtree G l.toFinset := by sorry

end ShortestConnection.Principles
