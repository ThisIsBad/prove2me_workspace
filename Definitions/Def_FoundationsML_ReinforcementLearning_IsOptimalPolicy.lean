import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.4 (Optimal policy; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 382, PDF p. 399): a policy `π*` is optimal if
`∀ π, ∀ s, V_{π*}(s) ≥ V_π(s)`. -/
def IsOptimalPolicy {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) : Prop :=
  ∀ π' : S → A → ℝ, IsPolicy π' → ∀ s : S, PolicyValue π' P Er γ s ≤ PolicyValue π P Er γ s

end FoundationsML.ReinforcementLearning
