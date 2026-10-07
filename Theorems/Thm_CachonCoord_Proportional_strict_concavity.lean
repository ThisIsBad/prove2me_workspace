import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 50: "The second order condition confirms each retailer's profit function is strictly
concave in his order quantity." For a buy-back rate `b < p` and any total stock `s ≥ 0` of the
other retailers, `x ↦ π_i(x, s)` is strictly concave on `x ≥ 0`. -/
theorem strict_concavity (M : Model) (w b s : ℝ) (hb : b < M.p) (hs : 0 ≤ s) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun x => M.retailerProfit w b x s) := by sorry

end CachonCoord.Proportional

