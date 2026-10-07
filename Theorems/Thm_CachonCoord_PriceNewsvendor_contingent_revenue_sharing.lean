import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 37 price-contingent revenue-sharing parameters reproduce the same
retailer-profit allocation as the contingent buyback, including goodwill costs. -/
theorem contingent_revenue_sharing (M : Model) (lam q p : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices) :
    let phi := lam + (lam * M.g - M.gr) / (p - M.v)
    let wr := lam * (M.c - M.v) - M.cr + phi * M.v
    M.revenueRetailer wr phi q p =
      lam * (M.Pi q p + M.g * M.mu p) - M.gr * M.mu p := by sorry

end CachonCoord.PriceNewsvendor

