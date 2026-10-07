import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_NPG_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.NPG

/-- Theorem 5.3 (global convergence for NPG; arXiv:1908.00261v5, p. 22): running the NPG
updates (15) with `ρ ∈ ∆(S)`, `θ^{(0)} = 0` and a fixed `η > 0`, for all `T > 0`,
`V^{(T)}(ρ) ≥ V^⋆(ρ) − log|A|/(ηT) − 1/((1−γ)²T)`. -/
theorem npg_global_convergence {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    [Nonempty A] (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (hη : 0 < η) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hθ0 : θ 0 = 0)
    (hrun : IsNPGRun P r γ ρ η θ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ) :
    ∀ T : ℕ, 0 < T →
      PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ - Real.log (Fintype.card A : ℝ) / (η * T) -
          1 / ((1 - γ) ^ 2 * T) ≤
        PolicyGradTheory.ProjGA.valueAt (softmaxPolicy (θ T)) P r γ ρ := by sorry

end PolicyGradTheory.NPG

