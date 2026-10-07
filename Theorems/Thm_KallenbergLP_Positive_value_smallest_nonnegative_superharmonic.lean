import Definitions.Def_KallenbergLP_Positive_Value

namespace KallenbergLP.Positive

/-- Theorem 3.5.1: the extended value is nonnegative and satisfies the
Bellman superharmonic inequalities; every nonnegative real superharmonic
vector is an upper bound. -/
theorem value_smallest_nonnegative_superharmonic
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α] (M : MDP N α)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a) :
    (∀ i : Fin N, (0 : EReal) ≤ value M i) ∧
    (∀ i (a : α), a ∈ M.actions i →
      (↑(M.reward i a) : EReal) +
        ∑ j : Fin N, (↑(M.transition i a j) : EReal) * value M j ≤ value M i) ∧
    (∀ w : Fin N → ℝ, (∀ i, 0 ≤ w i) → IsSuperharmonic M w →
      ∀ i, value M i ≤ (↑(w i) : EReal)) := by sorry

end KallenbergLP.Positive

