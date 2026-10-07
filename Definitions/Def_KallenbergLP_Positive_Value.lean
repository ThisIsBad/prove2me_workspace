import Definitions.Def_KallenbergLP_Positive_Policy

namespace KallenbergLP.Positive

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- Expected reward at time `n + 1`, conditional on the initial state. -/
def stageReward (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a ∈ M.actions j, occupancy M R i j a n * M.reward j a

/-- Total expected reward, defined as the supremum of finite partial sums.
Under nonnegative rewards this is exactly the limit in §2.2, including `+∞`. -/
noncomputable def totalReward (M : MDP N α) (R : Policy M) (i : Fin N) : EReal :=
  ⨆ n : ℕ, (↑(∑ t ∈ Finset.range n, stageReward M R i t) : EReal)

/-- Componentwise TMD value over all admissible history-dependent policies. -/
noncomputable def value (M : MDP N α) (i : Fin N) : EReal :=
  ⨆ R : Policy M, totalReward M R i

/-- Definition 3.3.1, with its original real-valued domain. -/
def IsSuperharmonic (M : MDP N α) (w : Fin N → ℝ) : Prop :=
  ∀ i (a : α), a ∈ M.actions i →
    M.reward i a + ∑ j : Fin N, M.transition i a j * w j ≤ w i

end KallenbergLP.Positive
