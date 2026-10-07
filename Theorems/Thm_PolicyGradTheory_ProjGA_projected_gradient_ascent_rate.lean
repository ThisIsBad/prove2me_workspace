import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Theorem 4.1, arXiv:1908.00261v5, p. 15: projected gradient ascent (9) on `V^π(μ)` with step
size `η = (1−γ)³/(2γ|A|)`, from any initial policy, satisfies, for every distribution `ρ`,
`V⋆(ρ) − V^{(t)}(ρ) ≤ ε` for some `t ≤ T` whenever `T > 64γ|S||A|/((1−γ)⁶ε²) · D²`, where `D` is
any bound `d^{π⋆}_ρ ≤ D μ` on the distribution mismatch coefficient `‖d^{π⋆}_ρ/μ‖_∞`. The index
range `t ≤ T` is the one the proof (p. 50) establishes; the printed `t < T` fails at `T = 1`. -/
theorem projected_gradient_ascent_rate {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (hγ : 0 < γ) (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj)
    (π : ℕ → EuclideanSpace ℝ (S × A)) (hπ0 : π 0 ∈ simplexSet S A)
    (hrun : IsProjGARun P r γ μ ((1 - γ) ^ 3 / (2 * γ * (Fintype.card A : ℝ))) Proj π)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ T : ℕ,
      64 * γ * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2 <
          (T : ℝ) →
        ∃ t ≤ T, valueAt πstar P r γ ρ - valueAt (asPolicy (π t)) P r γ ρ ≤ ε := by sorry

end PolicyGradTheory.ProjGA

