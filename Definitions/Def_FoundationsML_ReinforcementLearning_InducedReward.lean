import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- The expected reward vector induced by a (possibly stochastic) policy `π` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 386,
PDF p. 403, notation `R_s = E[r(s,π(s))]` used in Proposition 17.9 and Theorem 17.10):
`R_s = ∑_a π(s)(a) E[r(s,a)]`, the expected reward marginalized over the mixed action
distribution `π(s)`. -/
noncomputable def InducedReward {S A : Type*} [Fintype A]
    (π : S → A → ℝ) (Er : S → A → ℝ) (s : S) : ℝ :=
  ∑ a : A, π s a * Er s a

end FoundationsML.ReinforcementLearning
