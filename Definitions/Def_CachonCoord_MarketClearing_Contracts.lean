import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- Resale price maintenance with floor price `p̄` (§6.5.2, pp. 56–57): expected revenue per
unit of stock when the retailers' total stock is `Q`. In each state, if the market clearing price
is at least `p̄` all stock sells at that price; otherwise only the demand at `p̄` sells (`1 − p̄` in
the low state, `θ(1 − p̄)` in the high state), at `p̄`, allocated in proportion to stock. -/
noncomputable def rpmUnitRevenue (θ pbar Q : ℝ) : ℝ :=
  (1 / 2) * (if pbar ≤ pl Q then pl Q else pbar * (1 - pbar) / Q) +
  (1 / 2) * (if pbar ≤ ph θ Q then ph θ Q else pbar * (θ * (1 - pbar)) / Q)

/-- Expected profit `π_r(t)` of a retailer holding `y = q(t)` units under resale price maintenance
`(p̄, w)` when the retailers' total stock is `Q` (§6.5.2, p. 56). -/
noncomputable def rpmRetailerProfit (θ pbar w Q y : ℝ) : ℝ :=
  y * rpmUnitRevenue θ pbar Q - w * y

/-- Units sold in the low state under a buy-back `b`: the market price cannot fall below `b`, so
the retailers sell `min(q, 1 − b)` (§6.5.2, p. 57). -/
noncomputable def bbSalesLow (b q : ℝ) : ℝ := min q (1 - b)

/-- Units sold in the high state under a buy-back `b`: `min(q, θ(1 − b))` (§6.5.2, p. 57). -/
noncomputable def bbSalesHigh (θ b q : ℝ) : ℝ := min q (θ * (1 - b))

/-- The retailers' expected profit with a buy-back contract `(w, b)` and total order `q`: sales at
the market clearing price, `b` per returned unit, `w` per unit ordered (§6.5.2, p. 57). -/
noncomputable def bbRetailerProfit (θ b w q : ℝ) : ℝ :=
  (1 / 2) * (pl (bbSalesLow b q) * bbSalesLow b q + b * (q - bbSalesLow b q)) +
  (1 / 2) * (ph θ (bbSalesHigh θ b q) * bbSalesHigh θ b q + b * (q - bbSalesHigh θ b q)) -
  w * q

/-- The supplier's expected profit with a buy-back contract `(w, b)` and total order `q`:
`wq` minus the expected buy-back payments; production cost zero (§6.5.2, p. 57). -/
noncomputable def bbSupplierProfit (θ b w q : ℝ) : ℝ :=
  w * q - (1 / 2) * b * (q - bbSalesLow b q) - (1 / 2) * b * (q - bbSalesHigh θ b q)

end CachonCoord.MarketClearing
