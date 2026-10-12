import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h : ℝ) (hht : t / y < h) :
    P.real {ω | x ≤ St X yv ω} ≤
      Real.exp (h * (muY P X yv - x) + 1 / 2 * Real.exp t * B2Y P X yv * h ^ 2 +
        (Real.exp (h * y) - 1 - h * y) / y ^ t * AY P X yv t) := by sorry

end NagaevLD.FukNagaev

