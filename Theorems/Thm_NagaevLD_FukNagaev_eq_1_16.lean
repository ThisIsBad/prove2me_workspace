import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (h : ℝ) (hht : t / b < h) :
    ∫ ω in {ω | t / h < X ω}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
      (∫ ω in {ω | 0 ≤ X ω}, X ω ^ t ∂P) * (Real.exp (h * b) - 1 - h * b) / b ^ t := by sorry

end NagaevLD.FukNagaev

