import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 5 (Stone 1977, p. 609). Under (1)–(4), for `r ≥ 1` and a Borel `f` with `E|f(X)|ʳ < ∞`,
`∑ᵢ W_{ni}(X) f(Xᵢ) → f(X)` in `Lʳ`, i.e. `E|∑ᵢ W_{ni}(X) f(Xᵢ) − f(X)|ʳ → 0`. -/
theorem proposition_5 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (h4 : Cond4 μ W)
    (r : ℝ) (hr : 1 ≤ r) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hfr : ∫⁻ x, ‖f x‖ₑ ^ r ∂μ < ∞) :
    Tendsto (fun n => ∫⁻ ω,
        ‖∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1)) - f (ω 0)‖ₑ ^ r ∂(xLaw μ)) atTop (𝓝 0) := by sorry

end StoneRegression.Criterion

