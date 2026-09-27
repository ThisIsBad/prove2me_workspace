import Mathlib

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.2 (Policy; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 381, PDF p. 398). A (stationary) policy is a mapping
`π : S → Δ(A)`, a probability distribution over actions at each state.

**Formalization Note.** `π : S → A → ℝ` with `IsPolicy π` asserting `π s` is a probability
distribution over the finite type `A`, for every `s`, rather than a `PMF`-valued function —
matches Theorem 17.7's own quantification "for any pair `(s,a)` with `π(s)(a) > 0`" directly. -/
def IsPolicy {S A : Type*} [Fintype A] (π : S → A → ℝ) : Prop :=
  ∀ s : S, (∀ a : A, 0 ≤ π s a) ∧ ∑ a : A, π s a = 1

end FoundationsML.ReinforcementLearning
