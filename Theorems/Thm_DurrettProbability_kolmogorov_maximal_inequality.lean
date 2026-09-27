import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem kolmogorov_maximal_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = 0)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (μ {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|}).toReal
      ≤ Var[partialSum X n; μ] / x ^ 2 := by sorry

end DurrettProbability
