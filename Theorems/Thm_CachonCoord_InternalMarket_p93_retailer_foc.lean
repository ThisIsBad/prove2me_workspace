import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, p. 93, retailer `i`'s first-order condition (Cachon 2003, 3rd draft): with demand
realization `αᵢ > 0`, elasticity `η > 1` and per-unit price `w > 0`, the profit
`πᵢ(q, w) = αᵢ q^{(η−1)/η} − w q` has derivative `((η − 1)/η) αᵢ q^{−1/η} − w` at every `q > 0`, and a
quantity `q ≥ 0` maximizes `πᵢ(·, w)` over `[0, ∞)` if and only if `q > 0` and
`((η − 1)/η) αᵢ q^{−1/η} − w = 0`. -/
theorem p93_retailer_foc (η αᵢ w : ℝ) (hη : 1 < η) (hα : 0 < αᵢ) (hw : 0 < w) :
    (∀ q : ℝ, 0 < q →
      HasDerivAt (retailerProfit η αᵢ w) ((η - 1) / η * αᵢ * q ^ (-1 / η) - w) q) ∧
    ∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η αᵢ w) (Set.Ici 0) q ↔
        0 < q ∧ (η - 1) / η * αᵢ * q ^ (-1 / η) - w = 0) := by sorry

end CachonCoord.InternalMarket

