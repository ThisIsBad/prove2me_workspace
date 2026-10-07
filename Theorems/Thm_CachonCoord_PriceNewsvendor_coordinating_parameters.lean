import Mathlib
import Definitions.Def_CachonCoord_PriceNewsvendor_Model

namespace CachonCoord.PriceNewsvendor

/-- The p. 35 price-contingent terms satisfy the buyback coordination equations
(5) and (6) at each price. -/
theorem coordinating_parameters (M : Model) (lam p : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hp : p ∈ M.demand.prices) :
    p - M.v + M.gr - M.contingentB lam p = lam * (p - M.v + M.g) ∧
    M.contingentW lam p - M.contingentB lam p + M.cr - M.v =
      lam * (M.c - M.v) := by sorry

end CachonCoord.PriceNewsvendor

