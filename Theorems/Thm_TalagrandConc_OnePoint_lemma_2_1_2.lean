import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem lemma_2_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (ENNReal.ofReal (g ω))⁻¹ ∂μ) *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (aOne t) := by sorry

end TalagrandConc.OnePoint

