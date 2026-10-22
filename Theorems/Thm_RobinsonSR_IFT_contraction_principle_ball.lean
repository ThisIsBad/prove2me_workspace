import Mathlib

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46, the contraction principle as invoked there: a self-map `Φ` of
the closed ball `V_ε = closedBall x₀ ρ` (`ρ > 0`) of a Banach space that is a contraction with
modulus `κ ∈ [0, 1)` on it has a unique fixed point `x_p ∈ V_ε`, and
`‖x_p − x‖ ≤ (1 − κ)⁻¹ ‖Φ x − x‖` for every `x ∈ V_ε` (bound (2.5), with `κ = λδ`). -/
theorem contraction_principle_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (x0 : X) (rho : ℝ) (hrho : 0 < rho) (Φ : X → X)
    (hmaps : Set.MapsTo Φ (Metric.closedBall x0 rho) (Metric.closedBall x0 rho))
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk1 : kappa < 1)
    (hcontr : ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖Φ x₁ - Φ x₂‖ ≤ kappa * ‖x₁ - x₂‖) :
    ∃ xp ∈ Metric.closedBall x0 rho, Φ xp = xp ∧
      (∀ z ∈ Metric.closedBall x0 rho, Φ z = z → z = xp) ∧
      ∀ x ∈ Metric.closedBall x0 rho, ‖xp - x‖ ≤ (1 - kappa)⁻¹ * ‖Φ x - x‖ := by sorry

end RobinsonSR.IFT

