import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46: `‖Φ_p(x₁) − Φ_p(x₂)‖ ≤ λδ‖x₁ − x₂‖` on `V_ε`, where
`Φ_p(x) = s (r(p, x))`. -/
theorem contraction_estimate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (U : Set (StrongDual ℝ X)) (s : StrongDual ℝ X → X) (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hdelta0 : 0 < delta) (hballΩ : Metric.closedBall x0 rho ⊆ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta) :
    ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖s (residual f f' p0 x0 p x₁) - s (residual f f' p0 x0 p x₂)‖ ≤
        lam * delta * ‖x₁ - x₂‖ := by sorry

end RobinsonSR.IFT

