import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem rationing_nash_inflates (h p r A1 Qstar Q : ℝ) (Dlaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dlaw]
    (hh : 0 < h) (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hA : 0 < A1)
    (hint : ∀ y : ℝ, MeasureTheory.Integrable (fun d => h * max (y - d) 0 + p * max (d - y) 0) Dlaw)
    (hFc : Continuous (ProbabilityTheory.cdf Dlaw))
    (hFmono : StrictMonoOn (ProbabilityTheory.cdf Dlaw) (Set.Ici 0))
    (hQs0 : 0 ≤ Qstar) (hQstar : ProbabilityTheory.cdf Dlaw Qstar = p / (h + p))
    (hA2 : A1 < 2 * Qstar) (hQpos : 0 < Q)
    (hNash : ∀ Q1 : ℝ, 0 < Q1 →
      rationingCost h p r A1 Dlaw Q Q ≤ rationingCost h p r A1 Dlaw Q Q1) :
    Qstar < Q := by sorry

end SupplyChainTheory

