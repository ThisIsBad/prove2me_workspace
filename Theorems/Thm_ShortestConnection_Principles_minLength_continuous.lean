import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §III, p. 1394: the length `L` of a shortest spanning subtree of a connected
labelled graph `G`, the smallest of the finitely many spanning subtree lengths, depends
continuously on the edge lengths `w` (product topology on `Sym2 V → ℝ`).
Implicit hypothesis made explicit: `G` is connected (so spanning subtrees exist). -/
theorem minLength_continuous {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    Continuous (fun w : Sym2 V → ℝ => minLength G w) := by sorry

end ShortestConnection.Principles
