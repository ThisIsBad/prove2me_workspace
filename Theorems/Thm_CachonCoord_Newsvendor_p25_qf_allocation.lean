import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25 — profit allocation under the quantity flexibility contract
`(w_q(δ), δ)`: at δ = 0 the retailer earns `Π(q°) + g_s(μ − S(q°) + F̄(q°)q°) ≥ Π(q°)`; at δ = 1
the supplier earns `Π(q°) + μg_r ≥ Π(q°)`; and, the profits being continuous in δ, every
allocation of `Π(q°)` (retailer `a`, supplier `Π(q°) − a`, `0 ≤ a ≤ Π(q°)`) arises for some
`δ ∈ [0, 1]`. Standing assumption `Π(q°) > 0` (p. 11). -/
theorem p25_qf_allocation (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) (hPi : 0 < chainProfit P D q0) :
    (retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) ∧
      chainProfit P D q0 ≤
        retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0) ∧
    (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr ∧
      chainProfit P D q0 ≤
        supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0) ∧
    ∀ a ∈ Set.Icc 0 (chainProfit P D q0), ∃ δ ∈ Set.Icc (0 : ℝ) 1,
      retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 = a ∧
      supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 =
        chainProfit P D q0 - a := by sorry

end CachonCoord.Newsvendor

