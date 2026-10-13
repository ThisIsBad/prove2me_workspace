import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Corollary 7.5.9, p. 148. If the (CAV) assumptions hold for the distinguished
state `z` and the `z` standard policy `d`, then the (BOR) assumptions hold (for `z`, `d` and
some `ε > 0`). -/
theorem bor_of_cav {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hCAV : CAVAssumptions M z d) :
    ∃ ε : ℝ, BORAssumptions M z d ε := by sorry

end SennottDP.BOR

