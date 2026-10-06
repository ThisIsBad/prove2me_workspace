import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

namespace ChenBullwhip.Centralized

theorem lemma_2_1 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) :
    ∀ i ∈ Finset.Icc 1 p,
      ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C p t) P = 0 := by sorry

end ChenBullwhip.Centralized

