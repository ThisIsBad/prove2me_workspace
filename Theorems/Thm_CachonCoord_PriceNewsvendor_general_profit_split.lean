import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 36 algebraic allocation for arbitrary goodwill penalties, with the
mean demand evaluated at the chosen retail price. -/
theorem general_profit_split (M : Model) (lam q p : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hq : 0 ≤ q) (hp : p ∈ M.demand.prices) :
    M.buybackRetailer (M.contingentW lam p) (M.contingentB lam p) q p =
      lam * (M.Pi q p + M.g * M.mu p) - M.gr * M.mu p ∧
    M.buybackSupplier (M.contingentW lam p) (M.contingentB lam p) q p =
      (1 - lam) * M.Pi q p - (lam * M.g - M.gr) * M.mu p := by sorry

end CachonCoord.PriceNewsvendor

