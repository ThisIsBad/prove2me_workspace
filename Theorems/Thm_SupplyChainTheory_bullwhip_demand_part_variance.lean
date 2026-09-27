import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_demand_part_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P)
    (L m : ℕ) (hm : 0 < m) (t : ℤ) :
    ProbabilityTheory.variance
        (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω) P
      = (1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m))
          * ProbabilityTheory.variance (X.D t) P := by sorry

end SupplyChainTheory

