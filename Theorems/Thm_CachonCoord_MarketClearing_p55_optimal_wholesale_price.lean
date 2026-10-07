import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 55: over the wholesale prices `0 ≤ w < 1`, the supplier's profit `π_s(w)` is maximized at
`w*(θ)` (`1/2` if `θ ≤ 3`, `1/4` otherwise), with `π_s(w*(θ)) = θ/(2(1+θ))` if `θ ≤ 3` and `θ/8`
otherwise. -/
theorem p55_optimal_wholesale_price (θ : ℝ) (hθ : 1 < θ) :
    IsMaxOn (supplierProfit θ) (Set.Ico 0 1) (wStar θ) ∧
    supplierProfit θ (wStar θ) = (if θ ≤ 3 then θ / (2 * (1 + θ)) else θ / 8) := by sorry

end CachonCoord.MarketClearing

