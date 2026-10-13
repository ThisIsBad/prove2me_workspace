import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory

/-- Equations (24) and (25), in the proof of Lemma 18, p. 1882. -/
theorem eq_24_iff_eq_25 (μ : ℕ → ℕ → ℝ)
    (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1) :
    (∀ i j, μ i j = μ (i + 1) j + μ i (j + 1)) ↔
      ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by sorry

end LambdaCoalescent.Rates

