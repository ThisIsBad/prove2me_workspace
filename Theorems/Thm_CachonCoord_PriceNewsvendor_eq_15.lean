import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- Equation (15) against (14), p. 34, in the zero-goodwill regime. If the quantity-flexibility
contract `(w_q, δ)`, `0 ≤ δ ≤ 1`, leaves an interior integrated-optimal price `p` (at fixed
`q > 0`) optimal for the retailer, then `w_q = v - c_r` or `δ = 0`. The price derivative of
`∫_{(1-δ)q}^q F(y|p) dy` is taken, as on the page, to be `∫_{(1-δ)q}^q ∂F(y|p)/∂p dy`
(differentiation under the integral sign, a disclosed regularity hypothesis). -/
theorem eq_15 (M : Model) (q p wq δ Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p)
    (hFint : IntervalIntegrable (fun y => M.demand.priceSlope y p) MeasureTheory.volume
      ((1 - δ) * q) q)
    (hI : HasDerivAt (fun t => ∫ y in (1 - δ) * q..q, cdfOf (M.demand.law t) y)
      (∫ y in (1 - δ) * q..q, M.demand.priceSlope y p) p)
    (hchain : IsMaxOn (fun t => M.Pi q t) M.demand.prices p)
    (hret : IsMaxOn (fun t => M.qfRetailer wq δ q t) M.demand.prices p) :
    wq = M.v - M.cr ∨ δ = 0 := by sorry

end CachonCoord.PriceNewsvendor

