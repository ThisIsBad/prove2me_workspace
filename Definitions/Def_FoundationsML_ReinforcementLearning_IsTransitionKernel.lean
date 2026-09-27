import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.1 (MDP transition probability; Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, p. 380, PDF p. 397): `P[s'|s,a]`, a distribution
over destination states `s'`, for every `(s,a) ∈ S × A`.

**Formalization Note.** `P : S → A → S → ℝ` with `IsTransitionKernel P` asserting `P s a` is a
probability distribution over the finite type `S`, for every `(s,a)`. -/
def IsTransitionKernel {S A : Type*} [Fintype S] (P : S → A → S → ℝ) : Prop :=
  ∀ (s : S) (a : A), (∀ s' : S, 0 ≤ P s a s') ∧ ∑ s' : S, P s a s' = 1

end FoundationsML.ReinforcementLearning
