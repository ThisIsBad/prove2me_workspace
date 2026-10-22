import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology

theorem ae_tendsto_of_regular17 {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : Regular17 E)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (Y : Ω → E) (hY : Measurable Y) (hXY : TendstoInMeasure μ X atTop Y) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => X i ω) atTop (𝓝 (Y ω)) := by sorry

end StochIneqPO.Monotone

