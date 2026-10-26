import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 3 (Stone 1977, p. 609). Weights (of any sign) satisfying (1)–(3), constants `Mₙ, Nₙ ≥ 0`
with `P(Mₙ ≤ ∑ᵢ W²_{ni}(X) ≤ Nₙ) → 1`, and a nonnegative Borel `f` with `Ef(X) < ∞`. Then
`liminf E ∑ᵢ W²_{ni}(X) f(Xᵢ) ≥ (liminf Mₙ) Ef(X)` and `limsup E ∑ᵢ W²_{ni}(X) f(Xᵢ) ≤ (limsup Nₙ) Ef(X)`,
all in `ℝ≥0∞`. -/
theorem proposition_3 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (M N : ℕ → ℝ≥0)
    (hMN : Tendsto (fun n => xLaw μ {ω | (M n : ℝ) ≤ ∑ i : Fin n, wAt W n ω i ^ 2 ∧
        ∑ i : Fin n, wAt W n ω i ^ 2 ≤ (N n : ℝ)}) atTop (𝓝 1))
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, f x ∂μ < ∞) :
    liminf (fun n => (M n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ ≤
        liminf (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i ^ 2) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ∧
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i ^ 2) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ≤
        limsup (fun n => (N n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ := by sorry

end StoneRegression.Criterion

