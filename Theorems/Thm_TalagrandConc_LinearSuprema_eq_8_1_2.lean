import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic

namespace TalagrandConc.LinearSuprema

theorem eq_8_1_2 {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ENNReal.ofReal (linearSupremum F (fun i => r i + x i) - a) ≤
      ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by sorry

end TalagrandConc.LinearSuprema

