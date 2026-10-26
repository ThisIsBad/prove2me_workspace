import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 8 (Stone 1977, p. 610). Let `Y₁, Y₂, …` be i.i.d. standard normal and independent of
`(X, X₁, X₂, …)`; these are the response coordinates of `pairLaw μ (Kernel.const _ (gaussianReal 0 1))`
(the response paired with `X` itself is also present there, and unused). If `∑ᵢ W_{ni}(X) Yᵢ → 0` in
probability, then `∑ᵢ W²_{ni}(X) → 0` in probability. -/
theorem proposition_8 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (hY : TendstoInMeasure (pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1)))
      (fun n ω => estimate W n ω) atTop (fun _ => 0)) :
    TendstoInMeasure (xLaw μ) (fun n ω => ∑ i : Fin n, wAt W n ω i ^ 2) atTop (fun _ => 0) := by sorry

end StoneRegression.Criterion

