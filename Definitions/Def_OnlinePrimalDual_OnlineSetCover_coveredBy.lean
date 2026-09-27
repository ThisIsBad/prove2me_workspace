import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance

namespace OnlinePrimalDual.OnlineSetCover

/-- Element `e` is covered by the current cover `C`, i.e. `e ∈ C̄` in the book's notation
(p. 136, PDF p. 47: "Define `C̄` to be the union of all the elements covered by members of
`C`"): some chosen set `t ∈ C` contains `e`. -/
def coveredBy {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (C : Finset T) (e : E) : Prop :=
  ∃ t ∈ inst.elemSets e, t ∈ C

end OnlinePrimalDual.OnlineSetCover
