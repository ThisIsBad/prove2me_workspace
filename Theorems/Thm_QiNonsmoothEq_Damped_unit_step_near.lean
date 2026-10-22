import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem unit_step_near {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (hB : ∀ y, BDiffAt F y)
    (β σ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hrun : IsDampedNewtonRun F 1 β σ x d α) (hne : ∀ k, F (x k) ≠ 0)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hzero : F xstar = 0) (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    ∃ δbar > 0, ∀ k, ‖x k - xstar‖ ≤ δbar →
      α k = 1 ∧ x (k + 1) = x k + d k ∧ ‖x (k + 1) - xstar‖ ≤ (1 / 2) * ‖x k - xstar‖ := by sorry

end QiNonsmoothEq.Damped

