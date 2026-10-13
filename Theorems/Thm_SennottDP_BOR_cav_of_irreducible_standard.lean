import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Corollary 7.5.10, p. 149. Assume (CAV*): (CAV*1) there is a standard policy
`d` (here: `z` standard for the state `z`) with `R_d = S`; (CAV*2) for every `U > 0` the set
`D_U = {i | C(i,a) ≤ U for some a}` is finite. Then the (CAV) assumptions hold, and hence (BOR)
is valid (for `z`, `d` and some `ε > 0`). -/
theorem cav_of_irreducible_standard {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hd : IsZStandard d.toPolicy z)
    (hR : recClass M d z = Set.univ)
    (hD : ∀ U : ℝ, 0 < U → (lowCostSet M (ENNReal.ofReal U)).Finite) :
    CAVAssumptions M z d ∧ ∃ ε : ℝ, BORAssumptions M z d ε := by sorry

end SennottDP.BOR

