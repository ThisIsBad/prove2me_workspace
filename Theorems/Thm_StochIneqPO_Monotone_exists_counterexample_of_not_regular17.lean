import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

namespace StochIneqPO.Monotone

open MeasureTheory Filter

theorem exists_counterexample_of_not_regular17 {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : ¬ Regular17 E) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ ω, Monotone fun i => X i ω) ∧
        (∃ z : E, TendstoInMeasure μ X atTop (fun _ => z)) ∧ ¬ ConvergesAS μ X := by sorry

end StochIneqPO.Monotone

