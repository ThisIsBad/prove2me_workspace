import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 7 (Stone 1977, p. 610). If the weights are nonnegative and
`limsup_n E ∑ᵢ W_{ni}(X) f(Xᵢ) < ∞` for every nonnegative Borel `f` with `Ef(X) < ∞`, then there are a
positive integer `n₀` and a positive constant `C` such that, for every nonnegative Borel `f`,
`E ∑ᵢ W_{ni}(X) f(Xᵢ) ≤ C Ef(X)` for all `n ≥ n₀`. The `n₀` and `C` are chosen before `f`. -/
theorem proposition_7 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (hbdd : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∫⁻ x, f x ∂μ < ∞ →
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
        ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop < ∞) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ C : ℝ≥0, 0 < C ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∀ n, n₀ ≤ n →
        ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) ≤
          C * ∫⁻ x, f x ∂μ := by sorry

end StoneRegression.Criterion

