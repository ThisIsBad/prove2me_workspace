import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem theorem_1_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : β = 1 - α)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) :
    (cond_1_4 t α β x y (B2Y P X yv) (AY P X yv t) →
        P.real {ω | x ≤ S n X ω} ≤
          ∑ i, P.real {ω | yv i < X i ω} + P6 t α x (muY P X yv) (B2Y P X yv)) ∧
      (cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t) →
        P.real {ω | x ≤ S n X ω} <
          ∑ i, P.real {ω | yv i < X i ω} + P4 t α β x y (muY P X yv) (AY P X yv t)) ∧
      (cond_1_6 t α β x y (B2Y P X yv) (AY P X yv t) →
        (β ≥ t * α / 2 ∨ β * x ≥ muY P X yv) →
        P.real {ω | x ≤ S n X ω} <
          ∑ i, P.real {ω | yv i < X i ω} + P5 t α β x y (muY P X yv) (AY P X yv t)) := by sorry

end NagaevLD.FukNagaev

