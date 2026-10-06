import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem order_variance {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L p t) P
      = (1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p))
            * ProbabilityTheory.variance (X.D t) P
        + 2 * z * (1 + 2 * (L : ℝ) / p)
            * ProbabilityTheory.covariance (X.D (t - 1)) (X.sigmaHat C p t) P
        + z ^ 2 * ProbabilityTheory.variance
            (fun ω => X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) P := by sorry

end ChenBullwhip.Centralized

