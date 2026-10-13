import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem demand_count_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (S.demandCount t ω : ENNReal) ∂P = ENNReal.ofReal (∫ s in (0 : ℝ)..t, S.rate s) := by sorry

end ServiceParts.NonstatPalm

