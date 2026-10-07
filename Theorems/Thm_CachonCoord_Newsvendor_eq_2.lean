import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.1, Eq. (2), p. 11: the unique channel-optimal order
quantity has critical fractile `F̄(q°) = (c − v)/(p − v + g)`. -/
theorem eq_2 (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D)
    (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    1 - cdf D q0 = (P.c - P.v) / (P.r - P.v + P.p) ∧
      ∀ q : ℝ, IsMaxOn (chainProfit P D) Set.univ q → q = q0 := by sorry

end CachonCoord.Newsvendor

