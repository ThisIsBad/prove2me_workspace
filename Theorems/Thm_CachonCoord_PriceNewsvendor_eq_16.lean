import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- Equation (16) against (14), p. 35, in the zero-goodwill regime. If a buy-back contract
with fixed terms `(w_b, b)` leaves an interior integrated-optimal price `p` (at fixed `q`)
optimal for the retailer, and expected sales have a nonzero price derivative there, then
`b = -g_s`; moreover any `λ` for which `(w_b, b)` satisfies (5)–(6) forces `w_b = c_s - g_s`. -/
theorem eq_16 (M : Model) (q p wb b Sp : ℝ)
    (hgr : M.gr = 0) (hgs : M.gs = 0)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices)
    (hS : HasDerivAt (fun t => M.S q t) Sp p) (hSp : Sp ≠ 0)
    (hchain : IsMaxOn (fun t => M.Pi q t) M.demand.prices p)
    (hret : IsMaxOn (fun t => M.buybackRetailer wb b q t) M.demand.prices p) :
    b = -M.gs ∧
    ∀ lam : ℝ, p - M.v + M.gr - b = lam * (p - M.v + M.g) →
      wb - b + M.cr - M.v = lam * (M.c - M.v) → wb = M.cs - M.gs := by sorry

end CachonCoord.PriceNewsvendor

