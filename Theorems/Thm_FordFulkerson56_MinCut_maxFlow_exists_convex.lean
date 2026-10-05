import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow

namespace FordFulkerson56.MinCut

theorem maxFlow_exists_convex {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) :
    (∃ f, IsMaxFlow N f) ∧ Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} := by sorry

end FordFulkerson56.MinCut

