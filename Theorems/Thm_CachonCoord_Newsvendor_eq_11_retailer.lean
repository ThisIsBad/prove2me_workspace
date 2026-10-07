import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, Eq. (11) and the concavity argument, p. 24:
the wholesale price `w_q(δ)` makes the retailer's first-order condition zero
at the channel optimum, which maximizes the retailer's profit under forced
compliance. -/
theorem eq_11_retailer (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D)
    (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    HasDerivAt (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ)) 0 q0 ∧
    IsMaxOn (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ)) Set.univ q0 := by sorry

end CachonCoord.Newsvendor

