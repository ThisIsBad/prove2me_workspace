import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), 3rd draft, §6.2.1, p. 10: for a demand law on `[0, ∞)` with finite mean,
expected sales `S(q) = E[min(q, D)] = q − ∫_0^q F(y) dy`, expected leftover inventory
`I(q) = E[(q − D)⁺] = q − S(q)` and expected lost sales `L(q) = E[(D − q)⁺] = μ − S(q)`. -/
theorem p10_expected_sales (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x) (q : ℝ) :
    expSales D q = q - ∫ y in (0 : ℝ)..q, cdf D y ∧
      expLeftover D q = q - expSales D q ∧
      ∫ d, max (d - q) 0 ∂D = meanDemand D - expSales D q := by sorry

end CachonCoord.Newsvendor

