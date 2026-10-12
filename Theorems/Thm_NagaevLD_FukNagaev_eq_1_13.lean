import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (b : ℝ) (hb : 0 < b) (hXb : P {ω | b < X ω} = 0)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : MemLp X 2 P) (h : ℝ) (hh : 0 < h) (hht : h ≤ t / b) :
    ∫ ω in {ω | X ω ≤ b}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ∧
      ∫ ω in {ω | X ω ≤ t / h}, (Real.exp (h * X ω) - 1 - h * X ω) ∂P ≤
        Real.exp t * (∫ ω, X ω ^ 2 ∂P) * h ^ 2 / 2 := by sorry

end NagaevLD.FukNagaev

