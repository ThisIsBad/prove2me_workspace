import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, proof of Theorem 5.1, (5.3)–(5.5), p. 239: if `F` is B-differentiable at a zero
`x*` and `‖h‖ ≤ c ‖F'(x*; h)‖` for all `h` (5.3), then for every `δ₁ > 0` there is
`δ ∈ (0, δ₁)` with `‖y - x*‖ ≤ 2c ‖F(y)‖` whenever `‖y - x*‖ ≤ δ` (5.5). -/
theorem error_bound_5_5 {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hBx : QiNonsmoothEq.Local.BDiffAt F xstar) (hzero : F xstar = 0)
    (c : ℝ) (hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖) :
    ∀ δ₁ : ℝ, 0 < δ₁ → ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧
      ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ → ‖y - xstar‖ ≤ 2 * c * ‖F y‖ := by sorry

end QiNonsmoothEq.Attraction

