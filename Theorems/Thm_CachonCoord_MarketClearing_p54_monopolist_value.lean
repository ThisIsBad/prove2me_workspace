import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 54: the monopolist's expected profit is
`Π° = (1/2)p_l(1/2)(1/2) + (1/2)p_h(θ/2)(θ/2) = (1 + θ)/8`, and this is the largest expected profit
she can obtain by ordering a stock and selling any part of it in each demand state; the stock
`θ/2`, selling `1/2` in the low state and `θ/2` in the high state, attains it. -/
theorem p54_monopolist_value (θ : ℝ) (hθ : 1 < θ) :
    (1 / 2) * pl (1 / 2) * (1 / 2) + (1 / 2) * ph θ (θ / 2) * (θ / 2) = (1 + θ) / 8 ∧
    (1 / 2 : ℝ) ≤ θ / 2 ∧
    IsGreatest (monopolyOutcomes θ) ((1 + θ) / 8) := by sorry

end CachonCoord.MarketClearing

