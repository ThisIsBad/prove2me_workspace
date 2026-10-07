import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 16, "Theorem 8" (the chapter's third theorem),
p. 241: under the standing assumption `r₃ > r₄` of § 15, if
`D = q₁ r₂ r₃ + q₂ r₁ r₄ − q₃ r₁ r₂ < 0`, the problem of maximizing `f(∞)` never uses a
`C`-policy and has the two-choice form of Theorem 1: a two-choice control following the rule of
Theorem 1 exists and is optimal among all three-choice controls, and every optimal three-choice
control has `φ₃ = 0` almost everywhere. -/
theorem theorem8_negative_D_two_choice (P : Params) (hP : P.Positive) (hr : P.r₄ < P.r₃)
    (hD : D P < 0) (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁) ∧
    (∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁ →
      IsOptimalInfty P x₀ y₀ (twoChoice φ₁)) ∧
    ∀ φ : Control, IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), φ 2 t = 0 := by sorry

end BellmanDP.ContGoldMining

