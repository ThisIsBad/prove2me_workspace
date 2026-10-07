import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- On p. 36 the printed equality of price derivatives omits the factor `φ`.
With no goodwill penalty and `φ > 0`, revenue sharing has exactly the chain's
price maximizers for each fixed quantity. -/
theorem revenue_sharing_price (M : Model) (q p phi wr Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0) (hphi : 0 < phi)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) :
    HasDerivAt (fun t => M.Pi q t) (M.S q p + (p - M.v) * Sp) p ∧
    HasDerivAt (fun t => M.revenueRetailer wr phi q t)
      (phi * (M.S q p + (p - M.v) * Sp)) p ∧
    (IsMaxOn (fun t => M.Pi q t) M.demand.prices p ↔
     IsMaxOn (fun t => M.revenueRetailer wr phi q t) M.demand.prices p) := by sorry

end CachonCoord.PriceNewsvendor

