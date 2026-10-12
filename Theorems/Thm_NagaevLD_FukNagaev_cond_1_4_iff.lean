import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem cond_1_4_iff (t : ℝ) (ht : 2 ≤ t) (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : β = 1 - α) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy0 : 0 < y) (B A : ℝ) (hB : 0 < B)
    (hA : 0 < A) :
    cond_1_4 t α β x y B A ↔
      α * x / (Real.exp t * B) ≤
        max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) := by sorry

end NagaevLD.FukNagaev

