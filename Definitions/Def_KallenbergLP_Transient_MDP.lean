import Mathlib
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- The finite substochastic Markov decision system of §2.2, without a reward criterion. -/
structure MDP (N : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  states_nonempty : 0 < N
  actions : Fin N → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin N → α → Fin N → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_subprob : ∀ i a, a ∈ actions i →
    (∑ j : Fin N, transition i a j) ≤ 1

end KallenbergLP.Transient
