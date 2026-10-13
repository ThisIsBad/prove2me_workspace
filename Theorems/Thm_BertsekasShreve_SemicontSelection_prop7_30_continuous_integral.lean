import Mathlib

namespace BertsekasShreve.SemicontSelection

open MeasureTheory TopologicalSpace

/-- Proposition 7.30 (Bertsekas & Shreve, p. 145). Let `X`, `Y` be separable metrizable spaces and
`q(dy|x)` a continuous stochastic kernel on `Y` given `X` (a continuous map `X → P(Y)`, `P(Y)` with
the weak topology). If `f` is a bounded continuous real function on `X × Y`, then
`λ(x) = ∫ f(x, y) q(dy|x)` is continuous. -/
theorem prop7_30_continuous_integral {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : BoundedContinuousFunction (X × Y) ℝ) :
    Continuous (fun x => ∫ y, f (x, y) ∂(q x : Measure Y)) := by sorry

end BertsekasShreve.SemicontSelection

