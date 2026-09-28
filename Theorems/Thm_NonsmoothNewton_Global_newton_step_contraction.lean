import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Proof of Theorem 3.3 (Qi–Sun 1993, p. 360, second display): two consecutive Newton steps
taken from points of `S` contract by the factor `α = β (γ + δ)`. -/
theorem newton_step_contraction {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (xkm1 xk xkp1 : EuclideanSpace ℝ (Fin n)) (Vkm1 Vk : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hxkm1 : xkm1 ∈ Metric.closedBall x0 r) (hxk : xk ∈ Metric.closedBall x0 r)
    (hVkm1 : Vkm1 ∈ clarkeJac F xkm1) (hstepkm1 : Vkm1 (xk - xkm1) = -F xkm1)
    (hVk : Vk ∈ clarkeJac F xk) (hstepk : Vk (xkp1 - xk) = -F xk) :
    ‖xkp1 - xk‖ ≤ β * ‖F xk‖ ∧
      ‖xkp1 - xk‖ ≤ β * (δ + γ) * ‖xk - xkm1‖ := by sorry

end NonsmoothNewton.Global
