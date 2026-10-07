import Mathlib

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- p.21: the exponential distribution is the only continuous distribution on `[0, ∞)` with the
memoryless property (1.17). -/
theorem memoryless_only_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → ℝ) (hTm : Measurable T)
    (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (hnonneg : μ {ω | T ω < 0} = 0)
    (hmem : ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ →
      cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀}) :
    ∃ lam : ℝ, 0 < lam ∧ μ.map T = expMeasure lam := by sorry

end QueueingFundamentals.Foundations

