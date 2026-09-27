import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance

namespace OnlinePrimalDual.OnlineSetCover

/-- The weight of an element, `we := ∑_{s|e∈s} ws` (p. 136, PDF p. 47, "Let
`we = ∑_{s|e∈s} ws`"), given a (monotonically increasing, over the run) assignment `w` of
fractional weights to sets produced by Section 4.2's online fractional subroutine. -/
def elementWeight {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (e : E) : ℝ :=
  ∑ t ∈ inst.elemSets e, w t

end OnlinePrimalDual.OnlineSetCover
