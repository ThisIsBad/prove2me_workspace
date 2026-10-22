import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_QiNonsmoothEq_Local_Setting
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), Corollary 3.2, p. 235. Let `x*` be a zero of `F`, and let `F` be semismooth and
strongly BD-regular at `x*`. For every `ε > 0` (the page prints `ε ≥ 0`) there is `δ > 0` such that
for every `x` with `‖x - x*‖ ≤ δ` and every `V ∈ ∂_B F(x)`, `V` is nonsingular and
`‖x - V⁻¹F(x) - x*‖ ≤ ε ‖x - x*‖`, `‖F(x - V⁻¹F(x))‖ ≤ ε ‖F(x)‖`. -/
theorem corollary_3_2 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (xstar : EuclideanSpace ℝ (Fin n)) (hzero : F xstar = 0)
    (hss : NonsmoothNewton.Local.SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ →
      ∀ V ∈ NonsmoothNewton.Shared.bJac F y,
        (∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W) ∧
        ∀ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsInverse V W →
          ‖y - W (F y) - xstar‖ ≤ ε * ‖y - xstar‖ ∧
          ‖F (y - W (F y))‖ ≤ ε * ‖F y‖ := by sorry

end QiNonsmoothEq.Local

