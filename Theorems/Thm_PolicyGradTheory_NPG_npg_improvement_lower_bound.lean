import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_NPG_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.NPG

/-- Lemma 5.2 (improvement lower bound for NPG; arXiv:1908.00261v5, p. 23): for the NPG
iterates and every starting state distribution `µ`,
`V^{(t+1)}(µ) − V^{(t)}(µ) ≥ ((1−γ)/η) E_{s∼µ} log Z_t(s) ≥ 0`. -/
theorem npg_improvement_lower_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    [Nonempty A] (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (hη : 0 < η) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) :
    ∀ t : ℕ,
      (1 - γ) / η * ∑ s, μ s * Real.log (npgNormalizer P r γ η (θ t) s) ≤
          PolicyGradTheory.ProjGA.valueAt (softmaxPolicy (θ (t + 1))) P r γ μ - PolicyGradTheory.ProjGA.valueAt (softmaxPolicy (θ t)) P r γ μ ∧
        0 ≤ (1 - γ) / η * ∑ s, μ s * Real.log (npgNormalizer P r γ η (θ t) s) := by sorry

end PolicyGradTheory.NPG

