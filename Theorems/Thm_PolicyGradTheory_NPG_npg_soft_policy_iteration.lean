import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_NPG_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.NPG

/-- Lemma 5.1 (NPG as soft policy iteration; arXiv:1908.00261v5, p. 22), policy form: along any
run of the NPG updates (15) with softmax policies, from any start `θ^{(0)}`,
`π^{(t+1)}(a|s) = π^{(t)}(a|s) exp(η A^{(t)}(s,a)/(1−γ)) / Z_t(s)`. -/
theorem npg_soft_policy_iteration {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    [Nonempty A] (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ) :
    ∀ (t : ℕ) (s : S) (a : A),
      softmaxPolicy (θ (t + 1)) s a =
        softmaxPolicy (θ t) s a *
          Real.exp (η * PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a / (1 - γ)) /
          npgNormalizer P r γ η (θ t) s := by sorry

end PolicyGradTheory.NPG

