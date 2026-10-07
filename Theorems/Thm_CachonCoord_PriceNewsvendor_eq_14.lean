import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- Equation (14), p. 34, in the zero-goodwill regime in which `μ(p)` does not add a
price-derivative term. The chosen price is an interior price optimum at fixed quantity. -/
theorem eq_14 (M : Model) (q p Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p)
    (hmax : IsMaxOn (fun t => M.Pi q t) M.demand.prices p) :
    M.S q p + (p - M.v) * Sp = 0 := by sorry

end CachonCoord.PriceNewsvendor

