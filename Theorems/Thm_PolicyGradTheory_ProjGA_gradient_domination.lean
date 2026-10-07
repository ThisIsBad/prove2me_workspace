import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Lemma 4.1 (gradient domination), arXiv:1908.00261v5, p. 14: for the direct parameterization,
all state distributions `μ, ρ` and every policy `π`,
`V⋆(ρ) − V^π(ρ) ≤ ‖d^{π⋆}_ρ/d^π_μ‖_∞ max_{π̄} (π̄ − π)ᵀ∇_π V^π(μ)
  ≤ (1/(1−γ)) ‖d^{π⋆}_ρ/μ‖_∞ max_{π̄} (π̄ − π)ᵀ∇_π V^π(μ)`, the max over all policies `π̄`.
The max is passed as any upper bound `G`, the two mismatch coefficients as any `D₁`, `D` with
`d^{π⋆}_ρ ≤ D₁ d^π_μ` and `d^{π⋆}_ρ ≤ D μ` componentwise. -/
theorem gradient_domination {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A)
    (G : ℝ) (hG : ∀ πbar ∈ simplexSet S A,
      inner ℝ (πbar - π) (gradient (directValue P r γ μ) π) ≤ G)
    (D₁ : ℝ) (hD₁ : ∀ s, visitation πstar P γ ρ s ≤ D₁ * visitation (asPolicy π) P γ μ s)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s) :
    valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ D₁ * G ∧
      valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ 1 / (1 - γ) * D * G := by sorry

end PolicyGradTheory.ProjGA

