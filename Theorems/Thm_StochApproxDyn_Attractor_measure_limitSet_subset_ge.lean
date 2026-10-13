import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

universe u v

namespace StochApproxDyn.Attractor

/-- Theorem 7.3, second statement (Benaïm 1999, pp. 31–32). The numbers `T, δ` depend only on
`Φ`, `A` and `U`: they are chosen before the probability space, the process and `w`. -/
theorem measure_limitSet_subset_ge {M : Type u} [MetricSpace M] [LocallyCompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A)
    (U : Set M) (hU : IsOpen U) (hUc : IsCompact (closure U)) (hUB : closure U ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ (Ω : Type v) (m0 : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0),
          SatisfiesStandingAssumption Φ P ℱ X w →
          ∀ t : ℝ≥0,
            ENNReal.ofReal (1 - (w t δ T : ℝ)) * P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} ≤
              P {ω | StochApproxDyn.LimitSet.limitSet (fun s => X s ω) ⊆ A} := by sorry

end StochApproxDyn.Attractor

