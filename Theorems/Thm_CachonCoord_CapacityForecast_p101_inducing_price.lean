import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 101: with a wholesale price contract the supplier's
profit is `π_θ(k) = (w − c_p) S_θ(k) − c_k k`, and for every positive capacity `k` there is exactly
one wholesale price making `k` optimal for the supplier (a maximizer of `π_θ` over `k ≥ 0`), namely
`w_θ(k) = c_k / F̄_θ(k) + c_p`; such a price exists exactly when `F̄_θ(k) > 0`. -/
theorem p101_inducing_price (M : Model) (θ : DemandType) (k w : ℝ) (hk : 0 < k) :
    IsMaxOn (M.supWholesaleProfit θ w) (Set.Ici 0) k ↔
      (0 < 1 - cdf (M.μ θ) k ∧ w = M.wInduce θ k) := by sorry

end CachonCoord.CapacityForecast

