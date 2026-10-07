import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 57: under resale price maintenance with `p̄ = 1/2`, for a total order `1/2 < q < θ/2` a
retailer holding `q(t)` units earns `−q(t)w + (1/2)(((1/2)/q)q(t))p̄ + (1/2)q(t)(1 − q/θ)`; this is
strictly decreasing in `q` up to `θ/2`; with `w̄ = (1 + θ)/(4θ)` the competitive total order is
`θ/2`, and the supplier earns `w̄ · θ/2 = (1 + θ)/8 = Π°`. -/
theorem p57_rpm_order (θ : ℝ) (hθ : 1 < θ) :
    (∀ w Q y : ℝ, 1 / 2 < Q → Q < θ / 2 →
      rpmRetailerProfit θ (1 / 2) w Q y =
        -y * w + (1 / 2) * (((1 / 2) / Q) * y) * (1 / 2) + (1 / 2) * y * (1 - Q / θ)) ∧
    (∀ w y : ℝ, 0 < y →
      StrictAntiOn (fun Q => rpmRetailerProfit θ (1 / 2) w Q y) (Set.Ioc (1 / 2) (θ / 2))) ∧
    IsCompetitiveOrder (fun Q => rpmRetailerProfit θ (1 / 2) ((1 + θ) / (4 * θ)) Q Q) (θ / 2) ∧
    (1 + θ) / (4 * θ) * (θ / 2) = (1 + θ) / 8 := by sorry

end CachonCoord.MarketClearing

