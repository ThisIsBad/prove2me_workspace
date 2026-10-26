import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 6 (Stone 1977, pp. 609–610). Nonnegative weights such that `∑ᵢ W_{ni}(X) f(Xᵢ) → f(X)` in
probability for every bounded continuous `f` on `ℝᵈ` satisfy (3). -/
theorem proposition_6 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (hconv : ∀ f : EuclideanSpace ℝ (Fin d) →ᵇ ℝ, TendstoInMeasure (xLaw μ)
      (fun n ω => ∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1))) atTop (fun ω => f (ω 0))) :
    Cond3 μ W := by sorry

end StoneRegression.Criterion

