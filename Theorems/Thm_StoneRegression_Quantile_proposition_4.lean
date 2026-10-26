import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 4, p. 609: under (1)–(3), for every Borel `f` on `ℝᵈ` and every `ε > 0`,
`∑ᵢ |W_{ni}(X)| I{|f(Xᵢ) − f(X)| > ε} → 0` in probability. No integrability is assumed on `f`. -/
theorem proposition_4 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ StoneRegression.Criterion.Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ StoneRegression.Criterion.Cond2 μ W D) (h3 : StoneRegression.Criterion.Cond3 μ W)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε → TendstoInMeasure (StoneRegression.Criterion.xLaw μ)
      (fun n ω => ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then 1 else 0)) atTop (fun _ => 0) := by sorry

end StoneRegression.Quantile

