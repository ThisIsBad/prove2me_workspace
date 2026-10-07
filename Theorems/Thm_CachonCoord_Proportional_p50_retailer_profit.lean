import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 50, display of `π_i`: with proportional allocation, retailer `i`'s expected profit
under a buy-back contract `(w, b)` is
`π_i(q_i, q_{−i}) = (p − w) q_i − (p − b) (q_i/q) ∫_0^q F(x) dx`, `q = q_i + q_{−i}`. -/
theorem p50_retailer_profit (M : Model) (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * ∫ y in (0 : ℝ)..(x + s), M.F y := by sorry

end CachonCoord.Proportional

