import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 55: at the wholesale price `w*(θ)` the competitive retailers order
`q₁(w*(θ)) = θ/(1 + θ)` when `θ ≤ 3`, with market clearing prices `1/(1 + θ)` and `θ/(1 + θ)`,
and `q₂(w*(θ)) = θ/2` when `θ > 3`, with market clearing prices `0` and `1/2`. -/
theorem p55_market_prices (θ : ℝ) (hθ : 1 < θ) :
    (∃ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q) ∧
    ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q →
      (θ ≤ 3 → q = q1 θ (wStar θ) ∧ q1 θ (wStar θ) = θ / (1 + θ) ∧
        pl q = 1 / (1 + θ) ∧ ph θ q = θ / (1 + θ)) ∧
      (3 < θ → q = q2 θ (wStar θ) ∧ q2 θ (wStar θ) = θ / 2 ∧
        pl q = 0 ∧ ph θ q = 1 / 2) := by sorry

end CachonCoord.MarketClearing

