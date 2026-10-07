import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25: under the quantity flexibility contract `(w_q(δ), δ)` the
supplier's profit `π_s(q, w_q(δ), δ)` is differentiable at the chain-optimal `q°` with derivative
`g_s(1 − F(q°)) − c + v + (p − v + g_r)(1 − F(q°))`, and this derivative is `0`. -/
theorem p25_supplier_foc (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    HasDerivAt
        (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ))
        (P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0)) q0 ∧
      P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0) = 0 := by sorry

end CachonCoord.Newsvendor

