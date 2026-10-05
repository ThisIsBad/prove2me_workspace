import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain

namespace FordFulkerson56.MinCut

variable {V E : Type*} [DecidableEq E]

/-- A disconnecting set (Ford–Fulkerson, p. 400): a set of arcs meeting every chain joining the
source and the sink. -/
def IsDisconnecting (N : Network V E) (D : Finset E) : Prop :=
  ∀ C, IsChain N N.source N.sink C → (C ∩ D).Nonempty

/-- A cut (p. 400): a disconnecting set no proper subset of which is disconnecting. -/
def IsCut (N : Network V E) (D : Finset E) : Prop :=
  IsDisconnecting N D ∧ ∀ D' ⊂ D, ¬ IsDisconnecting N D'

/-- The value `v(D)` of a set of arcs: the sum of the capacities of its members (p. 400). -/
def cutValue (N : Network V E) (D : Finset E) : ℝ :=
  ∑ e ∈ D, N.cap e

end FordFulkerson56.MinCut
