import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem ar1_moments {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (t : ℤ) (k : ℕ) :
    (∫ ω, X.D t ω ∂P) = X.d / (1 - X.rho)
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2)
      ∧ ProbabilityTheory.covariance (X.D t) (X.D (t - k)) P
          = X.rho ^ k * ProbabilityTheory.variance (X.D t) P := by sorry

end SupplyChainTheory

