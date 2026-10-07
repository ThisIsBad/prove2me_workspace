import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 24: the quantity flexibility wholesale price
`w_q(δ) = (p − v + g_r)(1 − F(q°)) / (1 − F(q°) + (1 − δ)F((1 − δ)q°)) − c_r + v` satisfies
`w_q(0) = (p − v + g_r)F̄(q°) + v − c_r`, `w_q(1) = p + g_r − c_r`, is (strictly) increasing in
`δ ∈ [0, 1]`, and so lies in `[v − c_r, p + g_r − c_r]` for `δ ∈ [0, 1]`. -/
theorem p24_wq_range (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    quantityFlexPrice P D q0 0 = (P.r - P.v + P.pr) * (1 - cdf D q0) + P.v - P.cr ∧
      quantityFlexPrice P D q0 1 = P.r + P.pr - P.cr ∧
      StrictMonoOn (fun δ => quantityFlexPrice P D q0 δ) (Set.Icc 0 1) ∧
      ∀ δ ∈ Set.Icc (0 : ℝ) 1,
        P.v - P.cr ≤ quantityFlexPrice P D q0 δ ∧ quantityFlexPrice P D q0 δ ≤ P.r + P.pr - P.cr := by sorry

end CachonCoord.Newsvendor

