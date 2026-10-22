import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem corollary_3_4 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (xstar : EuclideanSpace ℝ (Fin n)) (hzero : F xstar = 0)
    (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ →
      ∀ dy : EuclideanSpace ℝ (Fin n), HasDirDerivAt F y dy (-F y) →
        ‖y + dy - xstar‖ ≤ ε * ‖y - xstar‖ ∧ ‖F (y + dy)‖ ≤ ε * ‖F y‖ := by sorry

end QiNonsmoothEq.Damped

