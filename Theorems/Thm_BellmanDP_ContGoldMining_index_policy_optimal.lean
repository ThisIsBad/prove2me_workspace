import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

/-- Bellman, *Dynamic Programming*, Ch. VIII, Theorem 1, p. 231: for the two-choice process
(7.2) under the constraints (7.3), the maximum of `f(∞)` is attained by the policy
`φ₁ = 1` for `q₁ r₂ y < q₂ r₁ x`, `φ₂ = 1` for `q₁ r₂ y > q₂ r₁ x`, and
`φ₁ = r₂/(r₁ + r₂)`, `φ₂ = r₁/(r₁ + r₂)` for `q₁ r₂ y = q₂ r₁ x`.
Stated as: an admissible control following this feedback rule along its own trajectory exists,
and every such control maximizes `f(∞)` over all admissible controls. -/
theorem index_policy_optimal (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁) ∧
    ∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁ →
      ∀ ψ₁ : ℝ → ℝ, TwoAdmissible ψ₁ →
        goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice ψ₁) ≤
          goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) := by sorry

end BellmanDP.ContGoldMining

