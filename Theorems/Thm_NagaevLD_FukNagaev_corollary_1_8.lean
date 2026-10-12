import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem corollary_1_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hAt : ∀ i, IntegrableOn (fun ω => |X i ω| ^ t) {ω | 0 ≤ X i ω} P) :
    P.real {ω | x ≤ S n X ω} ≤
      (1 + 2 / t) ^ t * Atplus P X t * x ^ (-t) +
        (if Bn2 P X = 0 then 0
          else Real.exp (-(2 * (t + 2) ^ (-2 : ℝ) * Real.exp (-t) * x ^ 2 / Bn2 P X))) := by sorry

end NagaevLD.FukNagaev

