import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem duopoly_newsvendor_capacity (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2) (c r : ℝ) (hc : 0 < c) (hcr : c < r)
    (xstar x1 x2 : ℝ) (hmono : P {ω | xstar < D1 ω + D2 ω} = ENNReal.ofReal (c / r))
    (hstrict : ∀ x, x < xstar → P {ω | xstar < D1 ω + D2 ω} < P {ω | x < D1 ω + D2 ω})
    (h1 : P {ω | effectiveDemand D1 D2 x2 ω ≤ x1} = ENNReal.ofReal (1 - c / r))
    (h2 : P {ω | effectiveDemand D2 D1 x1 ω ≤ x2} = ENNReal.ofReal (1 - c / r)) :
    xstar ≤ x1 + x2 := by sorry

end RevenueManagement
