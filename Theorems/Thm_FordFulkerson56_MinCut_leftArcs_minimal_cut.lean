import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
import Definitions.Def_FordFulkerson56_MinCut_leftArcs

namespace FordFulkerson56.MinCut

theorem leftArcs_minimal_cut {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    IsCut N (leftArcs N) ∧
    (∀ D : Finset E, IsDisconnecting N D → cutValue N (leftArcs N) ≤ cutValue N D) ∧
    ∀ f, IsMaxFlow N f → value f = cutValue N (leftArcs N) := by sorry

end FordFulkerson56.MinCut

