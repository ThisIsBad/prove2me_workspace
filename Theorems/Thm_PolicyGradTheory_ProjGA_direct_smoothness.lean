import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Lemma D.3 (smoothness for direct parameterization), arXiv:1908.00261v5, p. 74: for all
starting states `s₀` and all policies `π, π'`,
`‖∇_π V^π(s₀) − ∇_π V^{π'}(s₀)‖₂ ≤ (2γ|A|/(1−γ)³) ‖π − π'‖₂`. -/
theorem direct_smoothness {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ) :
    ∀ (s₀ : S), ∀ π ∈ simplexSet S A, ∀ π' ∈ simplexSet S A,
      ‖gradient (directValue P r γ (fun x => if x = s₀ then 1 else 0)) π -
          gradient (directValue P r γ (fun x => if x = s₀ then 1 else 0)) π'‖ ≤
        2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 * ‖π - π'‖ := by sorry

end PolicyGradTheory.ProjGA

