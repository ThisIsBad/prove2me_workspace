import Mathlib

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- Eq. (1.17) (pp.20–21): an exponentially distributed `T` is memoryless,
`Pr{T ≤ t_1 | T ≥ t_0} = Pr{0 ≤ T ≤ t_1 − t_0}` for `0 ≤ t_0 ≤ t_1`. -/
theorem exp_memoryless {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hTm : Measurable T)
    (hlaw : μ.map T = expMeasure lam) (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) :
    cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀} := by sorry

end QueueingFundamentals.Foundations

