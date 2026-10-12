import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem corollary_1_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hint : ∀ i, Integrable (X i) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (α β : ℝ) (hβ : β = t / (t + 2)) (hα : α = 1 - β)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) :
    P.real {ω | x ≤ S n X ω} ≤
      ∑ i, P.real {ω | yv i < X i ω} +
        (if B2Y P X yv = 0 then 0
          else Real.exp (-(α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X yv)))) +
        (AY P X yv t / (β * x * y ^ (t - 1))) ^ (β * x / y) := by sorry

end NagaevLD.FukNagaev

