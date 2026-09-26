import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem rm_duopoly_littlewood_monotone (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (D1 D2 : Ω → ℕ)
    (pL pH : ℝ) (hpH : 0 ≤ pH) (C y2 y2' : ℕ) (h : y2 ≤ y2') :
    littlewoodResponse P (spilloverDemand D1 D2 y2') pL pH C ≤
      littlewoodResponse P (spilloverDemand D1 D2 y2) pL pH C := by sorry

end RevenueManagement
