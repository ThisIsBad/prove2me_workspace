import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- The transition-probability matrix induced by a (possibly stochastic) policy `π`
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 385-386, PDF p. 402-403, notation `P_{s,s'} = P[s'|s,π(s)]` used in Proposition 17.9 and
Theorem 17.10): `P_{s,s'} = ∑_{a} π(s)(a) P[s'|s,a]`, the transition probability marginalized
over the mixed action distribution `π(s)`. -/
noncomputable def InducedTransition {S A : Type*} [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s s' : S) : ℝ :=
  ∑ a : A, π s a * P s a s'

end FoundationsML.ReinforcementLearning
