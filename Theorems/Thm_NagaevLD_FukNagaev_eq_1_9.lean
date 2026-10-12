import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (h : ℝ) (hh : 0 < h) :
    P.real {ω | x ≤ St X yv ω} ≤ Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P ∧
      Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P =
        Real.exp (-h * x) * ∏ i, ∫ ω, Real.exp (h * Xt X yv i ω) ∂P := by sorry

end NagaevLD.FukNagaev

