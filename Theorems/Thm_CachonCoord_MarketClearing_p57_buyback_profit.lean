import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 57: with a buy-back `b = 1/2` and a total order `1/2 < q < θ/2` the retailers' profit is
`(1/2)(p_l(1/2)(1/2) + b(q − 1/2)) + (1/2)(p_h(q)q) − qw = q(3/4 − w − q/(2θ))`; and with `w = 1/2`
their profit at `q = θ/2` is zero. -/
theorem p57_buyback_profit (θ : ℝ) (hθ : 1 < θ) :
    (∀ w q : ℝ, 1 / 2 < q → q < θ / 2 →
      bbRetailerProfit θ (1 / 2) w q =
          (1 / 2) * (pl (1 / 2) * (1 / 2) + (1 / 2) * (q - 1 / 2)) + (1 / 2) * (ph θ q * q) - q * w ∧
      bbRetailerProfit θ (1 / 2) w q = q * (3 / 4 - w - q / (2 * θ))) ∧
    bbRetailerProfit θ (1 / 2) (1 / 2) (θ / 2) = 0 := by sorry

end CachonCoord.MarketClearing

