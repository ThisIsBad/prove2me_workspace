import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- Lemma 7.1, second assertion (Benaïm 1999, p. 31): `Att(X)` is positively invariant under `Φ`. -/
theorem attainableSet_isPositivelyInvariant {Ω M : Type*} {m0 : MeasurableSpace Ω}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    IsPositivelyInvariant Φ (attainableSet P X) := by sorry

end StochApproxDyn.Attractor

