import Mathlib

namespace KallenbergLP.Bias

/-- The finite stochastic Markov decision model of §2.2 and the standing assumption of §5.2. -/
structure MDP (N : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  states_nonempty : 0 < N
  actions : Fin N → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin N → α → Fin N → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_sum_one : ∀ i a, a ∈ actions i →
    (∑ j : Fin N, transition i a j) = 1
  reward : Fin N → α → ℝ

end KallenbergLP.Bias
