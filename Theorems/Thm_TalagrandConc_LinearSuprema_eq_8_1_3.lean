import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic

namespace TalagrandConc.LinearSuprema

theorem eq_8_1_3 {N : ℕ} (F : Set (Fin N → ℝ))
    (hσfinite : BddAbove (coeffNorm '' F))
    (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hA : (linearSublevel F r a).Nonempty)
    (α : Fin N → ℝ) (hα : α ∈ F) :
    ∃ y ∈ linearSublevel F r a,
      ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => y i ≠ x i), |α i|) ≤
          ENNReal.ofReal (coeffNorm α) * convexDistance (linearSublevel F r a) x ∧
        ENNReal.ofReal (coeffNorm α) * convexDistance (linearSublevel F r a) x ≤
          ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by sorry

end TalagrandConc.LinearSuprema

