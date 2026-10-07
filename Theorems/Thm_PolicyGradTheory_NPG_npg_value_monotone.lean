import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_NPG_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.NPG

/-- §5.3, proof of Theorem 5.3 (arXiv:1908.00261v5, p. 24): the NPG iterates improve at every
state, `V^{(t+1)}(s) ≥ V^{(t)}(s)` for all states `s`. -/
theorem npg_value_monotone {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    [Nonempty A] (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (hη : 0 < η) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ) :
    ∀ (t : ℕ) (s : S),
      PolicyValue (softmaxPolicy (θ t)) P r γ s ≤
        PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s := by sorry

end PolicyGradTheory.NPG

