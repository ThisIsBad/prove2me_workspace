import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy
import Definitions.Def_ChenBullwhip_Centralized_Chain

namespace ChenBullwhip.Centralized

theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (p : ℕ) (hp : 1 ≤ p)
    (L : ℕ → ℕ) (C z : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (t : ℤ) :
    ProbabilityTheory.variance (X.chainOrder p L C z k t) P
          / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) / p
              + 2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)
      ∧ ((∀ i ∈ Finset.Icc 1 k, z i = 0) →
          ProbabilityTheory.variance (X.chainOrder p L C z k t) P
              / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) / p
              + 2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2)
                * (1 - X.rho ^ p)) := by sorry

end ChenBullwhip.Centralized

