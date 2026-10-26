import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem theorem_A_1_eps_zero {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcurv : ∀ i ≤ k, 0 < inner ℝ ((cg H g i).d) (H (cg H g i).d)) :
    (∀ i j, i ≤ k → j ≤ k → i ≠ j → inner ℝ ((cg H g i).d) (H (cg H g j).d) = 0) ∧
    Submodule.span ℝ ((fun i => (cg H g i).d) '' Set.Iic k) =
      Submodule.span ℝ ((fun i => (H ^ i) g) '' Set.Iic k) := by sorry

end TruncNewton.NegCurv

