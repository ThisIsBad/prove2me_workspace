import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46: `Φ_p(x) = s (r(p, x))` maps the closed ball `V_ε` of radius `ρ`
about `x₀` into itself. -/
theorem selfMap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (hU0 : (0 : StrongDual ℝ X) ∈ U)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta0 : 0 < delta) (hlamdelta : lam * delta < 1)
    (hball : Metric.closedBall x0 rho ⊆ V ∩ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta)
    (hN : lam * ‖f p0 x0 - f p x0‖ ≤ (1 - lam * delta) * rho) :
    ∀ x ∈ Metric.closedBall x0 rho,
      s (residual f f' p0 x0 p x) ∈ Metric.closedBall x0 rho := by sorry

end RobinsonSR.IFT

