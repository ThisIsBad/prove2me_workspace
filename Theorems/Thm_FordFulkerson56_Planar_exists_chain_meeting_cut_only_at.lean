import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting

namespace FordFulkerson56.Planar

/-- Proof of Theorem 2, p. 403: since `D` is a cut, for each arc `α ∈ D` there is a chain joining the
source and the sink which meets `D` in `α` only. -/
theorem exists_chain_meeting_cut_only_at {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E) (D : Finset E) (hD : FordFulkerson56.MinCut.IsCut N D) (α : E) (hα : α ∈ D) :
    ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C ∧ C ∩ D = {α} := by sorry

end FordFulkerson56.Planar

