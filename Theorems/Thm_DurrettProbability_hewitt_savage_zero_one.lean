import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem hewitt_savage_zero_one {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] (A : Set (ℕ → S)) (hA : IsPermutable A) :
    (Measure.infinitePi (fun _ : ℕ => μ)) A = 0
      ∨ (Measure.infinitePi (fun _ : ℕ => μ)) A = 1 := by sorry

end DurrettProbability
