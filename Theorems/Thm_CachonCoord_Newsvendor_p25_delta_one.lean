import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25 (δ = 1): with the quantity flexibility contract `(w_q(1), 1)` the
supplier's profit at `q°` is `g_sS(q°) + (p + g_r − c)q° − (p + g_r − v)∫_0^{q°} F(y)dy − μg_s
= Π(q°) + μg_r ≥ Π(q°)`. -/
theorem p25_delta_one (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        P.ps * expSales D q0 + (P.r + P.pr - P.c) * q0
          - (P.r + P.pr - P.v) * (∫ y in (0 : ℝ)..q0, cdf D y) - meanDemand D * P.ps ∧
      supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr ∧
      chainProfit P D q0 ≤
        supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 := by sorry

end CachonCoord.Newsvendor

