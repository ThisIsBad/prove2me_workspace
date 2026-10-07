import Mathlib

namespace KallenbergLP.OptTransient

/-- A finite Markov decision model with termination: transition rows may have mass below one. -/
structure FiniteSubstochasticMDP (n : ℕ) (α : Type) [Fintype α] [DecidableEq α] where
  n_pos : 0 < n
  actions : Fin n → Finset α
  actions_nonempty : ∀ i, (actions i).Nonempty
  transition : Fin n → α → Fin n → ℝ
  transition_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ transition i a j
  transition_sum_le_one : ∀ i a, a ∈ actions i → ∑ j, transition i a j ≤ 1
  reward : Fin n → α → ℝ

/-- Feasible state-action pairs of a finite decision model. -/
abbrev StateAction {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) : Type :=
  Σ i : Fin n, {a : α // a ∈ m.actions i}

end KallenbergLP.OptTransient
