import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 56: under resale price maintenance with `p̄ = 1/2` and total stock `θ/2`, a retailer
holding `q(t)` units earns `π_r(t) = −q(t)w + (1/2)(((1/2)/(θ/2))q(t))p̄ + (1/2)q(t)p̄
= q(t)((1 + θ)/(4θ) − w)`, which (for `q(t) > 0`) is zero exactly at `w̄ = (1 + θ)/(4θ)`. -/
theorem p56_rpm_profit (θ w y : ℝ) (hθ : 1 < θ) :
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y =
      -y * w + (1 / 2) * (((1 / 2) / (θ / 2)) * y) * (1 / 2) + (1 / 2) * y * (1 / 2) ∧
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y = y * ((1 + θ) / (4 * θ) - w) ∧
    (0 < y → (rpmRetailerProfit θ (1 / 2) w (θ / 2) y = 0 ↔ w = (1 + θ) / (4 * θ))) := by sorry

end CachonCoord.MarketClearing

