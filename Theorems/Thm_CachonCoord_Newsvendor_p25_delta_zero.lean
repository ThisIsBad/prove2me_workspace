import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25 (δ = 0): with the quantity flexibility contract `(w_q(0), 0)` the
retailer's profit at `q°` is `(p − v + g_r)S(q°) − ((p − v + g_r)/(p − v + g))(c − v)q° − μg_r
= Π(q°) + g_s(μ − S(q°) + F̄(q°)q°) ≥ Π(q°)`. -/
theorem p25_delta_zero (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        (P.r - P.v + P.pr) * expSales D q0
          - (P.r - P.v + P.pr) / (P.r - P.v + P.p) * (P.c - P.v) * q0 - meanDemand D * P.pr ∧
      retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) ∧
      chainProfit P D q0 ≤
        retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 := by sorry

end CachonCoord.Newsvendor

