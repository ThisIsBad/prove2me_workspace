import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 2 (Stone 1977, p. 608). Nonnegative weights satisfying (1)–(3), constants `Mₙ, Nₙ ≥ 0` with
`P(Mₙ ≤ ∑ᵢ W_{ni}(X) ≤ Nₙ) → 1`, and a nonnegative Borel `f` with `Ef(X) < ∞`. Then
`liminf E ∑ᵢ W_{ni}(X) f(Xᵢ) ≥ (liminf Mₙ) Ef(X)` and `limsup E ∑ᵢ W_{ni}(X) f(Xᵢ) ≤ (limsup Nₙ) Ef(X)`,
all in `ℝ≥0∞` (the limits inferior and superior may be `+∞`). -/
theorem proposition_2 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (M N : ℕ → ℝ≥0)
    (hMN : Tendsto (fun n => xLaw μ {ω | (M n : ℝ) ≤ ∑ i : Fin n, wAt W n ω i ∧
        ∑ i : Fin n, wAt W n ω i ≤ (N n : ℝ)}) atTop (𝓝 1))
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, f x ∂μ < ∞) :
    liminf (fun n => (M n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ ≤
        liminf (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ∧
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ≤
        limsup (fun n => (N n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ := by sorry

end StoneRegression.Criterion

