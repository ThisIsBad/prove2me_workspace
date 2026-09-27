import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.3 (Policy value, infinite discounted horizon; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 381, PDF p. 398):
`V_π(s) = E_{a_t∼π(s_t)}[∑_{t=0}^{+∞} γ^t r(s_t,a_t) | s_0 = s]`.

**Formalization Note.** `∑' t, γ^t * (∑_{s'} OccupationDist π P s t s' * InducedReward π Er
s')` computes exactly this expectation: `∑_{s'} OccupationDist π P s t s' * InducedReward π Er
s'` is `E[r(s_t,a_t) | s_0=s]` (average expected reward over the time-`t` state-occupation
distribution), and `∑'` (infinite sum, `tsum`) over `t` with the discount `γ^t` matches the
book's own infinite series. -/
noncomputable def PolicyValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (s : S) : ℝ :=
  ∑' t : ℕ, γ ^ t * ∑ s' : S, OccupationDist π P s t s' * InducedReward π Er s'

end FoundationsML.ReinforcementLearning
