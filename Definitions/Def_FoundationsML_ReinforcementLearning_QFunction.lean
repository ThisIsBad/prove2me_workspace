import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.5 (State-action value function; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 383, PDF p. 400, (17.1)):
`Q_π(s,a) = E[r(s,a) + γV_π(s_1) | s_0=s, a_0=a] = E[r(s,a)] + γ ∑_{s'} P[s'|s,a] V_π(s')`.

**Formalization Note.** Uses (17.1)'s own second (closed-form) equality directly as the
definition, rather than the first line's infinite-horizon expectation (which the book itself
shows equals this closed form via the one-step decomposition). -/
noncomputable def QFunction {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (s : S) (a : A) : ℝ :=
  Er s a + γ * ∑ s' : S, P s a s' * PolicyValue π P Er γ s'

end FoundationsML.ReinforcementLearning
