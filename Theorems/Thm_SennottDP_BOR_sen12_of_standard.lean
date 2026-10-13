import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Proposition 7.5.3, p. 143. If there exists a `z` standard (randomized
stationary) policy `d`, then (SEN1) and (SEN2) hold for `z`. -/
theorem sen12_of_standard {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy z) :
    SEN1 M z ∧ ∃ Mf : S → ℝ, SEN2 M z Mf := by sorry

end SennottDP.BOR

