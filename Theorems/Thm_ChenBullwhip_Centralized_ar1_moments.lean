import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem ar1_moments {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    ProbabilityTheory.covariance (X.D (t - 1)) (X.D (t - p - 1)) P
        = X.rho ^ p / (1 - X.rho ^ 2) * X.sigma ^ 2
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by sorry

end ChenBullwhip.Centralized

