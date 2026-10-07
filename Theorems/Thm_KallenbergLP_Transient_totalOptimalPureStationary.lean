import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.1: one pure stationary policy is total optimal for every initial state. -/
theorem totalOptimalPureStationary
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (h : TotalRewardExists M r) :
    ∃ f : PureRule M,
      ∀ i : Fin N, policyValue M r (purePolicy M f) i = valueVector M r i := by sorry

end KallenbergLP.Transient

