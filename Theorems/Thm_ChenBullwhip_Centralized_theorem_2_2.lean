import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem theorem_2_2 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L p t) P / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)
      ∧ (z = 0 →
          ProbabilityTheory.variance (X.order C z L p t) P / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)) := by sorry

end ChenBullwhip.Centralized

