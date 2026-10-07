import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, pp. 54–57. With wholesale price contracts the supplier's best profit is
`θ/(2(1+θ))` if `θ ≤ 3` and `θ/8` otherwise, attained at `w*(θ)`; it is strictly below the
monopolist's `Π° = (1 + θ)/8`; and with the full-refund buy-back `b = w = 1/2` the competitive
retailers order `θ/2` and the supplier earns `Π°`. -/
theorem sec_6_5_2_wholesale_vs_buyback (θ : ℝ) (hθ : 1 < θ) :
    IsGreatest (wholesaleOutcomes θ) (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) ∧
    (∃ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q) ∧
    (∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q →
      wStar θ * q = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8)) ∧
    IsGreatest (monopolyOutcomes θ) ((1 + θ) / 8) ∧
    (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) < (1 + θ) / 8 ∧
    IsCompetitiveOrder (bbRetailerProfit θ (1 / 2) (1 / 2)) (θ / 2) ∧
    bbSupplierProfit θ (1 / 2) (1 / 2) (θ / 2) = (1 + θ) / 8 := by sorry

end CachonCoord.MarketClearing

