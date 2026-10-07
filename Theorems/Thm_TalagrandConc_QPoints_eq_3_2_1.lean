import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic
import Definitions.Def_TalagrandConc_QPoints_aConst

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- (3.2.1) with `a(q, α)` of (3.2.2), for `α > 1`. -/
theorem eq_3_2_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (A : Fin q → Set (Fin N → Ω))
    (hA : ∀ i, MeasurableSet (A i)) (hf : Measurable (qDist A)) :
    ∫⁻ x, epow (ENNReal.ofReal (aConst q α)) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
      (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i) ^ α)⁻¹ := by sorry

end TalagrandConc.QPoints

