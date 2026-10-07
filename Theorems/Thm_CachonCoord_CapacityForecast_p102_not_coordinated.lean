import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 102: if `k* > 0` is a stationary point of the
manufacturer's wholesale-price profit `Π_θ(k) = (r − w_θ(k)) S_θ(k)` (`Π'_θ(k*) = 0`), where
`F̄_θ(k*) > 0` and `F_θ` has derivative `f_θ(k*) > 0` at `k*`, then
`F̄_θ(k*) = (c_k/(r − c_p)) (1 + f_θ(k*) S_θ(k*) / F̄_θ(k*)²) = F̄_θ(k_θ°) (1 + f_θ(k*) S_θ(k*) / F̄_θ(k*)²)`
for an optimal capacity `k_θ° > 0`, and the supply chain is not coordinated: `k* < k_θ°`. -/
theorem p102_not_coordinated (M : Model) (θ : DemandType) (kstar fk : ℝ) (hks : 0 < kstar)
    (hFbar : 0 < 1 - cdf (M.μ θ) kstar)
    (hf : HasDerivAt (cdf (M.μ θ)) fk kstar) (hfk : 0 < fk)
    (hstat : HasDerivAt (M.mfrWholesaleProfit θ) 0 kstar)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) (hko_pos : 0 < ko) :
    1 - cdf (M.μ θ) kstar
        = M.ck / (M.r - M.cp) * (1 + fk / (1 - cdf (M.μ θ) kstar) ^ 2 * M.S θ kstar) ∧
      1 - cdf (M.μ θ) kstar
        = (1 - cdf (M.μ θ) ko) * (1 + fk / (1 - cdf (M.μ θ) kstar) ^ 2 * M.S θ kstar) ∧
      kstar < ko := by sorry

end CachonCoord.CapacityForecast

