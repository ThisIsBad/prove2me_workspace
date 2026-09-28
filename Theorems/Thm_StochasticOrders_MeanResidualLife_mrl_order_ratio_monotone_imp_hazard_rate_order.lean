import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_HazardRateOrder

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

/-- Theorem 2.A.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 83): let `X` and
`Y` be two random variables (with the chapter's standing finite-mean hypothesis, so their mrl
functions `m`, `l` are genuinely `E[X-t∣X>t]`/`E[Y-t∣Y>t]`) with mrl functions `m` and `l`. Suppose
`m(t)/l(t)` increases in `t` (over the region `l(t) > 0` where the ratio is meaningful). Then, if
`X ≤mrl Y`, `X ≤hr Y`. -/
theorem mrl_order_ratio_monotone_imp_hazard_rate_order {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν)
    (hratio : MonotoneOn (fun t => mrl μ X t / mrl ν Y t) {t : ℝ | 0 < mrl ν Y t})
    (h : MrlOrder μ ν X Y) :
    HazardRateOrder μ ν X Y := by sorry

end StochasticOrders.MeanResidualLife

